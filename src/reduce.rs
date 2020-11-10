use crate::params::get_params;
use crate::{overhead, AllocatedNonNativeFieldVar};
use ark_ff::{biginteger::BigInteger, fields::FpParameters, BitIteratorBE};
use ark_ff::{One, PrimeField, Zero};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::AllocatedFp;
use ark_r1cs_std::{
    boolean::{AllocatedBit, Boolean},
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_relations::{
    lc,
    r1cs::{LinearCombination, Result as R1CSResult},
};
use ark_std::{cmp::min, marker::PhantomData, vec, vec::Vec};
use num_bigint::BigUint;
use num_integer::Integer;

pub fn limbs_to_bigint<BaseField: PrimeField>(
    bits_per_limb: usize,
    limbs: &[BaseField],
) -> BigUint {
    let mut val = BigUint::zero();
    let mut big_cur = BigUint::one();
    let two = BigUint::from(2u32);
    for limb in limbs.iter().rev() {
        let limb_repr = limb.into_repr().to_bits();
        let mut small_cur = big_cur.clone();
        for limb_bit in limb_repr.iter().rev() {
            if *limb_bit {
                val += &small_cur;
            }
            small_cur *= 2u32;
        }
        big_cur *= two.pow(bits_per_limb as u32);
    }

    val
}

pub fn bigint_to_basefield<BaseField: PrimeField>(bigint: &BigUint) -> BaseField {
    let mut val = BaseField::zero();
    let mut cur = BaseField::one();
    let bytes = bigint.to_bytes_be();

    let basefield_256 = BaseField::from_repr(<BaseField as PrimeField>::BigInt::from(256)).unwrap();

    for byte in bytes.iter().rev() {
        let bytes_basefield = BaseField::from(*byte as u128);
        val += cur * bytes_basefield;

        cur *= &basefield_256;
    }

    val
}

/// the collections of methods for reducing the presentations
pub struct Reducer<TargetField: PrimeField, BaseField: PrimeField> {
    pub target_phantom: PhantomData<TargetField>,
    pub base_phantom: PhantomData<BaseField>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> Reducer<TargetField, BaseField> {
    /// an internal method for checking whether the current two elements are ready to multiply;
    /// if not, they would be reduced. This is part of the pre-mul reduction.
    pub fn can_safely_mul(
        elem: &AllocatedNonNativeFieldVar<TargetField, BaseField>,
        other: &AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> bool {
        let params = get_params::<TargetField, BaseField>(&elem.cs);

        let prod_of_num_of_additions = (elem.num_of_additions_over_normal_form + BaseField::one())
            * (other.num_of_additions_over_normal_form + BaseField::one());

        let bits_per_limb = params.bits_per_limb;

        let overhead_limb = overhead!(prod_of_num_of_additions.mul(
            &BaseField::from_repr(<BaseField as PrimeField>::BigInt::from(
                (params.num_limbs) as u64
            ))
            .unwrap()
        ));

        let bits_per_mulresult_limb = 2 * (bits_per_limb + 1) + overhead_limb;

        bits_per_mulresult_limb < BaseField::size_in_bits()
    }

    /// convert limbs to bits (take at most `BaseField::size_in_bits() - 1` bits)
    /// This implementation would be more efficient than the original `to_bits`
    /// or `to_non_unique_bits` since we enforce that some bits are always zero.
    pub fn limb_to_bits(
        limb: &AllocatedFp<BaseField>,
        num_bits: usize,
    ) -> R1CSResult<Vec<Boolean<BaseField>>> {
        let cs = limb.cs.clone();

        let num_bits = min(BaseField::size_in_bits() - 1, num_bits);
        let mut bits_considered = Vec::with_capacity(num_bits);
        let limb_value = limb.value().unwrap_or_default();

        for b in BitIteratorBE::new(limb_value.into_repr()).skip(
            <<BaseField as PrimeField>::Params as FpParameters>::REPR_SHAVE_BITS as usize
                + (BaseField::size_in_bits() - num_bits),
        ) {
            bits_considered.push(b);
        }

        let mut bits = vec![];
        for b in bits_considered {
            bits.push(AllocatedBit::new_witness(
                ark_relations::ns!(cs, "bit"),
                || Ok(b),
            )?);
        }

        let mut lc = LinearCombination::zero();
        let mut coeff = BaseField::one();

        for bit in bits.iter().rev() {
            lc += (coeff, bit.variable());
            coeff.double_in_place();
        }

        let limb_lc = LinearCombination::from((BaseField::one(), limb.variable));

        limb.cs.enforce_constraint(lc!(), lc!(), limb_lc - lc)?;

        Ok(bits.into_iter().map(Boolean::from).collect())
    }

    /// A subprocedure of the common reduction, which firstly pushes the representations to the top
    pub fn push_to_the_top(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<(
        Vec<Boolean<BaseField>>,
        Vec<BaseField>,
        Vec<LinearCombination<BaseField>>,
    )> {
        let cs = elem.cs.clone();
        let params = get_params::<TargetField, BaseField>(&cs);

        let surfeit = overhead!(elem.num_of_additions_over_normal_form + BaseField::one()) + 1;
        let surfeit_plus_one = surfeit + 1; // one more bit is added as a result of pushing

        let mut limbs_value = Vec::<BaseField>::new();
        let mut limbs_lc = Vec::<LinearCombination<BaseField>>::new();
        let mut add: AllocatedFp<BaseField> =
            AllocatedFp::<BaseField>::new_constant(cs.clone(), &BaseField::zero())?;

        // non-top limbs
        for (i, limb) in elem
            .limbs
            .iter()
            .rev()
            .enumerate()
            .take(params.num_limbs - 1)
        {
            let limb_added = if i == 0 { limb.clone() } else { limb.add(&add) };

            let mut value = BaseField::zero();
            let mut lc = LinearCombination::<BaseField>::zero();
            let mut coeff = BaseField::one();

            let surfeit_cur = if i == 0 { surfeit } else { surfeit_plus_one };

            let limbs_bits = Self::limb_to_bits(&limb_added, params.bits_per_limb + surfeit_cur)?;

            for (_, bit) in limbs_bits
                .iter()
                .rev()
                .enumerate()
                .take(params.bits_per_limb)
            {
                if bit.value().unwrap_or_default() {
                    value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            limbs_value.push(value);
            limbs_lc.push(lc);

            coeff = BaseField::one();

            let mut add_value = BaseField::zero();
            lc = LinearCombination::<BaseField>::zero();
            for (_, bit) in limbs_bits
                .iter()
                .rev()
                .enumerate()
                .skip(params.bits_per_limb)
            {
                if bit.value().unwrap_or_default() {
                    add_value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            add =
                AllocatedFp::<BaseField>::new_witness(ark_relations::ns!(cs, "alloc_add"), || {
                    Ok(add_value)
                })?;

            let add_lc = LinearCombination::from((BaseField::one(), add.variable));

            cs.enforce_constraint(lc!(), lc!(), add_lc - lc)?;
        }

        let mut overhead_bits = Vec::<Boolean<BaseField>>::new();

        // top limb
        {
            let top_limb = &elem.limbs[0];
            let top_limb_added = top_limb.add(&add);

            let mut value = BaseField::zero();
            let mut lc = LinearCombination::<BaseField>::zero();
            let mut coeff = BaseField::one();

            let top_limbs_bits =
                Self::limb_to_bits(&top_limb_added, params.bits_per_limb + surfeit_plus_one)?;

            for (_, bit) in top_limbs_bits
                .iter()
                .rev()
                .enumerate()
                .take(params.bits_per_limb)
            {
                if bit.value().unwrap_or_default() {
                    value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            limbs_value.push(value);
            limbs_lc.push(lc);

            for bit in top_limbs_bits.iter().rev().skip(params.bits_per_limb) {
                overhead_bits.push((*bit).clone());
            }
        }

        limbs_value.reverse();
        limbs_lc.reverse();

        Ok((overhead_bits, limbs_value, limbs_lc))
    }

    /// Reduction to be enforced after additions
    pub fn post_add_reduce(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<()> {
        if Self::can_safely_push(elem) {
            Ok(())
        } else {
            Self::reduce_all_limbs(elem)
        }
    }

    /// an internal method for checking whether a push operation can be completed for the current gadget;
    /// if not, `reduce_all_limbs`, which reduces without using a push, is used.
    /// this is part of the post-add reduction.
    pub fn can_safely_push(elem: &AllocatedNonNativeFieldVar<TargetField, BaseField>) -> bool {
        let params = get_params::<TargetField, BaseField>(&elem.cs);

        let log = overhead!(elem.num_of_additions_over_normal_form + BaseField::one()) + 1;
        BaseField::size_in_bits() > params.bits_per_limb + log + 1
    }

    /// Use the `sum of resides` method to reduce the representations, without firstly pushing it to the top
    pub fn reduce_all_limbs(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<()> {
        let cs = elem.cs.clone();
        let params = get_params::<TargetField, BaseField>(&cs);

        // almost only used for mandatory reduce, since the values are not pushed first (pushing first provides better efficiency)
        let mut limb_bits = Vec::new();
        let surfeit = overhead!(elem.num_of_additions_over_normal_form + BaseField::one()) + 1;
        for limb in elem.limbs.iter() {
            limb_bits.push(Self::limb_to_bits(limb, params.bits_per_limb + surfeit)?);
        }

        // compute the powers of 2 mod p that might be used
        let mut powers_of_2_mod_p = Vec::new();
        let mut cur = TargetField::one();
        for _ in 0..params.num_limbs * params.bits_per_limb + surfeit {
            powers_of_2_mod_p.push(
                AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                    &cur,
                    Some(&cs),
                )
                .unwrap(),
            );
            cur.double_in_place();
        }

        // start with those bits that are within the weakly canonical representation
        let mut limbs_value = Vec::<BaseField>::new();
        let mut limbs_lc = Vec::<LinearCombination<BaseField>>::new();

        for limb in limb_bits.iter() {
            let mut value = BaseField::zero();
            let mut lc = LinearCombination::zero();
            let mut coeff = BaseField::one();

            let mut limb_rev = limb.clone();
            limb_rev.reverse();

            let num_bits_in_weakly_canonical = params.bits_per_limb;

            for (_, bit) in limb_rev
                .iter()
                .enumerate()
                .take(num_bits_in_weakly_canonical)
            {
                if bit.value().unwrap_or_default() {
                    value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            limbs_value.push(value);
            limbs_lc.push(lc);
        }

        let mut additions = BaseField::zero();
        for (i, limb) in limb_bits.iter().enumerate() {
            let mut limb_rev = limb.clone();
            limb_rev.reverse();

            let num_bits_in_weakly_canonical = params.bits_per_limb;

            for (j, bit) in limb_rev
                .iter()
                .enumerate()
                .skip(num_bits_in_weakly_canonical)
            {
                additions += &BaseField::one();
                let num_of_limbs_lower = params.num_limbs - i - 1;
                let power_of_2 = &powers_of_2_mod_p[num_of_limbs_lower * params.bits_per_limb + j];

                if bit.value().unwrap_or_default() {
                    for (k, power_of_2_limb) in power_of_2.iter().enumerate() {
                        limbs_value[k] += power_of_2_limb;
                    }
                }

                for (k, power_of_2_coeff) in power_of_2.iter().enumerate() {
                    limbs_lc[k] = &limbs_lc[k] + &(bit.lc() * *power_of_2_coeff);
                }
            }
        }

        let mut new_limbs_gadget = Vec::<AllocatedFp<BaseField>>::new();
        for (value, lc) in limbs_value.iter().zip(limbs_lc.iter()) {
            let value_gadget =
                AllocatedFp::<BaseField>::new_witness(elem.cs.clone(), || Ok(value))?;

            let value_lc = LinearCombination::from((BaseField::one(), value_gadget.variable));

            cs.enforce_constraint(lc!(), lc!(), value_lc - lc).unwrap();

            new_limbs_gadget.push(value_gadget.clone());
        }

        elem.limbs = new_limbs_gadget;
        elem.num_of_additions_over_normal_form = additions;

        Ok(())
    }

    /// A subprocedure of the common reduction, which pushes the representations to the top and keeps the new top unreduced.
    pub fn push_to_the_top_keep_top(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<(Vec<BaseField>, Vec<LinearCombination<BaseField>>)> {
        let cs = elem.cs.clone();
        let params = get_params::<TargetField, BaseField>(&cs);

        let surfeit = overhead!(elem.num_of_additions_over_normal_form + BaseField::one()) + 1;
        let surfeit_plus_one = surfeit + 1; // one more bit is added as a result of pushing

        let mut limbs_value = Vec::<BaseField>::new();
        let mut limbs_lc = Vec::<LinearCombination<BaseField>>::new();
        let mut add: AllocatedFp<BaseField> =
            AllocatedFp::<BaseField>::new_constant(cs.clone(), &BaseField::zero())?;

        // non-top limbs
        for (i, limb) in elem
            .limbs
            .iter()
            .rev()
            .enumerate()
            .take(params.num_limbs - 1)
        {
            let limb_added = if i != 0 { limb.add(&add) } else { limb.clone() };

            let mut value = BaseField::zero();
            let mut lc = LinearCombination::<BaseField>::zero();
            let mut coeff = BaseField::one();

            let surfeit_cur = if i != 0 { surfeit_plus_one } else { surfeit };

            let limbs_bits = Self::limb_to_bits(&limb_added, params.bits_per_limb + surfeit_cur)?;

            for (_, bit) in limbs_bits
                .iter()
                .rev()
                .enumerate()
                .take(params.bits_per_limb)
            {
                if bit.value().unwrap_or_default() {
                    value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            limbs_value.push(value);
            limbs_lc.push(lc);

            coeff = BaseField::one();

            let mut add_value = BaseField::zero();
            lc = LinearCombination::<BaseField>::zero();
            for (_, bit) in limbs_bits
                .iter()
                .rev()
                .enumerate()
                .skip(params.bits_per_limb)
            {
                if bit.value().unwrap_or_default() {
                    add_value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            add = AllocatedFp::<BaseField>::new_witness(cs.clone(), || Ok(add_value))?;

            let add_lc = LinearCombination::from((BaseField::one(), add.variable));
            cs.enforce_constraint(lc!(), lc!(), add_lc - lc)?;
        }

        // top limb
        {
            let top_limb = &elem.limbs[0];
            let top_limb_added = top_limb.add(&add);

            let lc = LinearCombination::from((BaseField::one(), top_limb_added.variable));

            limbs_value.push(top_limb_added.value().unwrap_or_default());
            limbs_lc.push(lc);
        }

        limbs_value.reverse();
        limbs_lc.reverse();

        Ok((limbs_value, limbs_lc))
    }

    /// A full reduction procedure, which pushes the representations to the top first and then reduces it
    pub fn push_and_reduce_the_top(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<()> {
        let surfeit = overhead!(elem.num_of_additions_over_normal_form + BaseField::one()) + 1;
        let cs = elem.cs.clone();

        let params = get_params::<TargetField, BaseField>(&cs);

        // push
        let (overhead_bits, mut limbs_value, mut limbs_lc) = Self::push_to_the_top(elem)?;

        // reduce
        let mut powers_of_2_mod_p = Vec::new();
        let mut cur = TargetField::one();
        let loop_length =
            (params.num_limbs - 1) * params.bits_per_limb + params.bits_per_limb + surfeit;
        for _ in 0..=loop_length {
            powers_of_2_mod_p.push(
                AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                    &cur,
                    Some(&cs),
                )
                .unwrap(),
            );
            cur.double_in_place();
        }

        let mut additions = BaseField::zero();
        for (i, bit) in overhead_bits.iter().enumerate() {
            additions += &BaseField::one();
            let power_of_2 = &powers_of_2_mod_p[params.num_limbs * params.bits_per_limb + i];

            if bit.value().unwrap_or_default() {
                for (j, power_of_2_limb) in power_of_2.iter().enumerate() {
                    limbs_value[j] += power_of_2_limb;
                }
            }

            for (j, power_of_2_coeff) in power_of_2.iter().enumerate() {
                limbs_lc[j] = &limbs_lc[j] + &(bit.lc() * *power_of_2_coeff);
            }
        }

        let mut new_limbs_gadget = Vec::<AllocatedFp<BaseField>>::new();
        for (value, lc) in limbs_value.iter().zip(limbs_lc.iter()) {
            let value_gadget = AllocatedFp::<BaseField>::new_witness(
                ark_relations::ns!(cs, "limb_initial_value_alloc"),
                || Ok(value),
            )?;

            let value_lc = (BaseField::one(), value_gadget.variable);

            let final_lc = LinearCombination::from(value_lc) - lc.clone();

            cs.enforce_constraint(lc!(), lc!(), final_lc).unwrap();

            new_limbs_gadget.push(value_gadget.clone());
        }

        elem.limbs = new_limbs_gadget;
        elem.num_of_additions_over_normal_form = additions;

        Ok(())
    }

    /// Reduction used before multiplication to reduce the representations in a way that allows efficient multiplication
    pub fn pre_mul_reduce(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
        elem_other: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<()> {
        let params = get_params::<TargetField, BaseField>(&elem.cs);

        if 2 * params.bits_per_limb + ark_std::log2(params.num_limbs) as usize
            > BaseField::size_in_bits() - 1
        {
            panic!("The current limb parameters do not support multiplication.");
        }

        while !Self::can_safely_mul(elem, elem_other) {
            if elem.num_of_additions_over_normal_form
                >= elem_other.num_of_additions_over_normal_form
            {
                Self::push_and_reduce_the_top(elem)?;
            } else {
                Self::push_and_reduce_the_top(elem_other)?;
            }
        }

        Ok(())
    }

    /// Reduction to the normal form
    pub fn pre_eq_reduce(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<()> {
        let cs = elem.cs.clone();
        let params = get_params::<TargetField, BaseField>(&cs);

        if elem.is_in_the_normal_form {
            return Ok(());
        }

        let value = elem.value().unwrap_or_default();
        let normal_form_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                &value,
                Some(&cs),
            )?;
        let normal_form_gadget =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::new_witness(cs.clone(), || {
                Ok(value)
            })?;

        let p_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations_from_big_int(
                &<TargetField as PrimeField>::Params::MODULUS,
                Some(&cs),
            )?;
        let mut p_gadget_limbs = Vec::new();
        for limb in &p_representations {
            p_gadget_limbs.push(AllocatedFp::<BaseField>::new_constant(cs.clone(), limb)?);
        }
        let p_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: cs.clone(),
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: BaseField::one(),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        let (elem_pushed_to_the_top_limbs_value, elem_pushed_to_the_top_limbs_lc) =
            Self::push_to_the_top_keep_top(elem)?;

        let elem_bigint =
            limbs_to_bigint(params.bits_per_limb, &elem_pushed_to_the_top_limbs_value);
        let normal_bigint = limbs_to_bigint(params.bits_per_limb, &normal_form_representations);
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let k = bigint_to_basefield::<BaseField>(&((elem_bigint - normal_bigint) / p_bigint));
        let k_gadget = AllocatedFp::<BaseField>::new_witness(cs.clone(), || Ok(k))?;

        // k should be smaller than 2^ ((BaseField::size_in_bits() - 1) - bits_per_limb - 1)
        // aka, k only has at most (BaseField::size_in_bits() - 1) - bits_per_limb - 1 bits.
        Self::limb_to_bits(
            &k_gadget,
            (BaseField::size_in_bits() - 1) - params.bits_per_limb - 1,
        )?;

        let mut kp_gadget_limbs = Vec::new();
        for limb in &p_gadget.limbs {
            kp_gadget_limbs.push(limb.mul(&k_gadget));
        }
        let kp_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: elem.cs.clone(),
            limbs: kp_gadget_limbs,
            num_of_additions_over_normal_form: elem.num_of_additions_over_normal_form,
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        let mut normal_form_plus_kp_gadget = normal_form_gadget.add(&kp_gadget)?;
        let (_, normal_form_plus_kp_limbs_lc) =
            Self::push_to_the_top_keep_top(&mut normal_form_plus_kp_gadget)?;

        for (left, right) in elem_pushed_to_the_top_limbs_lc
            .iter()
            .zip(normal_form_plus_kp_limbs_lc.iter())
        {
            let final_lc = left - right.clone();
            cs.enforce_constraint(lc!(), lc!(), final_lc)?;
        }

        elem.limbs = normal_form_gadget.limbs;
        elem.num_of_additions_over_normal_form = BaseField::zero();
        elem.is_in_the_normal_form = true;
        Ok(())
    }

    /// Group and check equality
    pub fn group_and_check_equality(
        cs: ConstraintSystemRef<BaseField>,
        surfeit: usize,
        bits_per_limb: usize,
        shift_per_limb: usize,
        left: &[AllocatedFp<BaseField>],
        right: &[AllocatedFp<BaseField>],
    ) -> Result<(), SynthesisError> {
        let zero = AllocatedFp::<BaseField>::new_constant(cs.clone(), BaseField::zero())?;

        let mut limb_pairs = Vec::<(AllocatedFp<BaseField>, AllocatedFp<BaseField>)>::new();
        let num_limb_in_a_group =
            (BaseField::size_in_bits() - 1 - surfeit - 1 - (bits_per_limb - shift_per_limb))
                / shift_per_limb;

        let shift_array = {
            let mut array = Vec::new();
            let mut cur = BaseField::one().into_repr();
            for _ in 0..num_limb_in_a_group {
                array.push(BaseField::from_repr(cur.clone()).unwrap());
                cur.muln(shift_per_limb as u32);
            }

            array
        };

        for (left_limb, right_limb) in left.iter().zip(right.iter()).rev() {
            // note: the `rev` operation is here, so that the first limb (and the first groupped limb) will be the least significant limb.
            limb_pairs.push((left_limb.clone(), right_limb.clone()));
        }

        let mut groupped_limb_pairs =
            Vec::<(AllocatedFp<BaseField>, AllocatedFp<BaseField>, usize)>::new();

        for limb_pairs_in_a_group in limb_pairs.chunks(num_limb_in_a_group) {
            let mut left_total_limb = zero.clone();
            let mut right_total_limb = zero.clone();

            for ((left_limb, right_limb), shift) in
                limb_pairs_in_a_group.iter().zip(shift_array.iter())
            {
                left_total_limb = left_total_limb.add(&left_limb.mul_constant(*shift));
                right_total_limb = right_total_limb.add(&right_limb.mul_constant(*shift));
            }

            groupped_limb_pairs.push((
                left_total_limb,
                right_total_limb,
                limb_pairs_in_a_group.len(),
            ));
        }

        // This part we mostly use the techniques in bellman-bignat
        // The following code is adapted from https://github.com/alex-ozdemir/bellman-bignat/blob/master/src/mp/bignat.rs#L567
        let mut carry_in = zero.clone();
        let mut accumulated_extra = BigUint::zero();
        for (group_id, (left_total_limb, right_total_limb, num_limb_in_this_group)) in
            groupped_limb_pairs.iter().enumerate()
        {
            let mut pad_limb_repr: <BaseField as PrimeField>::BigInt = BaseField::one().into_repr();
            pad_limb_repr.muln(
                (surfeit
                    + (bits_per_limb - shift_per_limb)
                    + shift_per_limb * num_limb_in_this_group
                    + 1) as u32,
            );
            let pad_limb = BaseField::from_repr(pad_limb_repr).unwrap();

            //println!("pad_limb = {:?}", pad_limb.into_repr());

            let left_total_limb_value = left_total_limb.value()?;
            let right_total_limb_value = right_total_limb.value()?;

            //println!("left_total_limb_value = {:?}", left_total_limb_value.into_repr());
            //println!("right_total_limb_value = {:?}", right_total_limb_value.into_repr());

            let carry_in_value = carry_in.value()?;

            let mut carry_value =
                left_total_limb_value + &carry_in_value + &pad_limb - &right_total_limb_value;

            //println!("left_total_limb_value + carry_in_value = {:?}", (left_total_limb_value + &carry_in_value).into_repr());
            //println!("left_total_limb_value + carry_in_value + pad_limb = {:?}", (left_total_limb_value + &carry_in_value + &pad_limb).into_repr());
            //println!("carry_value = {:?}", carry_value.into_repr());

            let mut carry_repr = carry_value.into_repr();
            carry_repr.divn((shift_per_limb * num_limb_in_this_group) as u32);

            carry_value = BaseField::from_repr(carry_repr).unwrap();

            let carry = AllocatedFp::<BaseField>::new_witness(cs.clone(), || Ok(carry_value))?;

            accumulated_extra += limbs_to_bigint(bits_per_limb, &vec![pad_limb]);

            let (new_accumulated_extra, remainder) = accumulated_extra.div_rem(
                &BigUint::from(2u64).pow((shift_per_limb * num_limb_in_this_group) as u32),
            );
            let remainder_limb = bigint_to_basefield::<BaseField>(&remainder);

            // Now check
            //      left_total_limb + pad_limb + carry_in - right_total_limb
            //   =  carry shift by (shift_per_limb * num_limb_in_this_group) + remainder

            //println!("carry_in = {:?}", carry_in_value.into_repr());
            //println!("carry = {:?}", carry_value.into_repr());

            let eqn_left = left_total_limb
                .add_constant(pad_limb)
                .add(&carry_in)
                .sub(&right_total_limb);

            //println!("left + pad = {:?}", left_total_limb.add_constant(pad_limb).value()?.into_repr());
            //println!("left + pad + carry_in = {:?}", left_total_limb
            //    .add_constant(pad_limb)
            //    .add(&carry_in).value()?.into_repr());

            let eqn_right = carry
                .mul_constant(
                    BaseField::from(2u64)
                        .pow(&vec![(shift_per_limb * num_limb_in_this_group) as u64]),
                )
                .add_constant(remainder_limb);

            //println!("left = {:?}", eqn_left.value()?.into_repr());
            //println!("right = {:?}", eqn_right.value()?.into_repr());

            eqn_left.conditional_enforce_equal(&eqn_right, &Boolean::<BaseField>::TRUE)?;

            accumulated_extra = new_accumulated_extra;
            carry_in = carry.clone();

            if group_id == groupped_limb_pairs.len() - 1 {
                carry.conditional_enforce_equal(
                    &AllocatedFp::<BaseField>::new_constant(
                        cs.clone(),
                        &bigint_to_basefield(&accumulated_extra),
                    )?,
                    &Boolean::<BaseField>::TRUE,
                )?;
            } else {
                Reducer::<TargetField, BaseField>::limb_to_bits(&carry, surfeit + bits_per_limb)?;
            }
        }

        println!("----------");

        Ok(())
    }
}
