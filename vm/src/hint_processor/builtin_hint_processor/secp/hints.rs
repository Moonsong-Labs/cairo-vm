use crate::stdlib::{
    collections::HashMap,
    ops::Deref,
    ops::{Add, Mul, Rem},
    prelude::*,
};

use crate::hint_processor::builtin_hint_processor::hint_utils::{
    get_constant_from_var_name, get_integer_from_var_name, get_relocatable_from_var_name,
    insert_value_from_var_name,
};
use crate::hint_processor::builtin_hint_processor::uint256_utils::Uint256;
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::math_utils::{div_mod, signed_felt};
use crate::serde::deserialize_program::ApTracking;
use crate::types::errors::math_errors::MathError;
use crate::types::exec_scope::ExecutionScopes;
use crate::types::relocatable::MaybeRelocatable;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::vm_core::VirtualMachine;
use crate::Felt252;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::Zero;
use num_traits::{FromPrimitive, One};

use super::bigint_utils::{BigInt3, Uint384};
use super::ec_utils::EcPoint;
use super::secp_utils::{BLS_BASE, BLS_PRIME, SECP256R1_ALPHA, SECP256R1_B, SECP256R1_P, SECP_P};

pub const SECP_REDUCE: &str = r#"from starkware.cairo.common.cairo_secp.secp256r1_utils import SECP256R1_P
from starkware.cairo.common.cairo_secp.secp_utils import pack
value = pack(ids.x, PRIME) % SECP256R1_P"#;
pub fn reduce_value(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let x = Uint384::from_var_name("x", vm, ids_data, ap_tracking)?.pack86();
    exec_scopes.insert_value("value", x.mod_floor(&SECP256R1_P));
    Ok(())
}

pub const SECP_REDUCE_X: &str = r#"from starkware.cairo.common.cairo_secp.secp256r1_utils import SECP256R1_P
from starkware.cairo.common.cairo_secp.secp_utils import pack

x = pack(ids.x, PRIME) % SECP256R1_P"#;
pub fn reduce_x(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let x = Uint384::from_var_name("x", vm, ids_data, ap_tracking)?.pack86();
    exec_scopes.insert_value("x", x.mod_floor(&SECP256R1_P));
    Ok(())
}

pub const COMPUTE_Q_MOD_PRIME: &str = r#"from starkware.cairo.common.cairo_secp.secp256r1_utils import SECP256R1_P
from starkware.cairo.common.cairo_secp.secp_utils import pack

q, r = divmod(pack(ids.val, PRIME), SECP256R1_P)
assert r == 0, f"verify_zero: Invalid input {ids.val.d0, ids.val.d1, ids.val.d2}."
ids.q = q % PRIME"#;
pub fn compute_q_mod_prime(
    vm: &mut VirtualMachine,
    _exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let val = Uint384::from_var_name("val", vm, ids_data, ap_tracking)?.pack86();
    let (q, r) = val.div_mod_floor(&SECP256R1_P);
    if !r.is_zero() {
        return Err(HintError::SecpVerifyZero(Box::new(val)));
    }
    insert_value_from_var_name("q", Felt252::from(&q), vm, ids_data, ap_tracking)?;
    Ok(())
}

pub const COMPUTE_IDS_HIGH_LOW: &str = r#"from starkware.cairo.common.math_utils import as_int

# Correctness check.
value = as_int(ids.value, PRIME) % PRIME
assert value < ids.UPPER_BOUND, f'{value} is outside of the range [0, 2**165).'

# Calculation for the assertion.
ids.high, ids.low = divmod(ids.value, ids.SHIFT)"#;
pub fn compute_ids_high_low(
    vm: &mut VirtualMachine,
    _exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    const UPPER_BOUND: &str = "starkware.cairo.common.math.assert_250_bit.UPPER_BOUND";
    const SHIFT: &str = "starkware.cairo.common.math.assert_250_bit.SHIFT";
    //Declare constant values
    let upper_bound = constants
        .get(UPPER_BOUND)
        .map_or_else(|| get_constant_from_var_name("UPPER_BOUND", constants), Ok)?;
    let shift = constants
        .get(SHIFT)
        .map_or_else(|| get_constant_from_var_name("SHIFT", constants), Ok)?;
    let value = Felt252::from(&signed_felt(get_integer_from_var_name(
        "value",
        vm,
        ids_data,
        ap_tracking,
    )?));
    if &value > upper_bound {
        return Err(HintError::ValueOutside250BitRange(Box::new(value)));
    }

    let (high, low) = value.div_rem(&shift.try_into().map_err(|_| MathError::DividedByZero)?);
    insert_value_from_var_name("high", high, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name("low", low, vm, ids_data, ap_tracking)?;
    Ok(())
}

pub const SECP_R1_GET_POINT_FROM_X: &str = r#"from starkware.cairo.common.cairo_secp.secp_utils import SECP256R1, pack
from starkware.python.math_utils import y_squared_from_x

y_square_int = y_squared_from_x(
    x=pack(ids.x, SECP256R1.prime),
    alpha=SECP256R1.alpha,
    beta=SECP256R1.beta,
    field_prime=SECP256R1.prime,
)

# Note that (y_square_int ** ((SECP256R1.prime + 1) / 4)) ** 2 =
#   = y_square_int ** ((SECP256R1.prime + 1) / 2) =
#   = y_square_int ** ((SECP256R1.prime - 1) / 2 + 1) =
#   = y_square_int * y_square_int ** ((SECP256R1.prime - 1) / 2) = y_square_int * {+/-}1.
y = pow(y_square_int, (SECP256R1.prime + 1) // 4, SECP256R1.prime)

# We need to decide whether to take y or prime - y.
if ids.v % 2 == y % 2:
    value = y
else:
    value = (-y) % SECP256R1.prime"#;

pub fn r1_get_point_from_x(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    exec_scopes.insert_value::<BigInt>("SECP256R1_P", SECP256R1_P.clone());

    // def y_squared_from_x(x: int, alpha: int, beta: int, field_prime: int) -> int:
    // """
    // Computes y^2 using the curve equation:
    // y^2 = x^3 + alpha * x + beta (mod field_prime)
    // """
    // return (pow(x, 3, field_prime) + alpha * x + beta) % field_prime
    fn y_squared_from_x(x: &BigInt, alpha: &BigInt, beta: &BigInt, field_prime: &BigInt) -> BigInt {
        // Compute x^3 (mod field_prime)
        let x_cubed = x.modpow(&BigInt::from(3), field_prime);

        // Compute alpha * x
        let alpha_x = alpha.mul(x);

        // Compute y^2 = (x^3 + alpha * x + beta) % field_prime
        x_cubed.add(&alpha_x).add(beta).rem(field_prime)
    }

    // prime = curve.prime
    //     y_squared = y_squared_from_x(
    //         x=x,
    //         alpha=curve.alpha,
    //         beta=curve.beta,
    //         field_prime=prime,
    //     )

    //     y = pow(y_squared, (prime + 1) // 4, prime)
    //     if (y & 1) != request.y_parity:
    //         y = (-y) % prime

    let x = Uint384::from_var_name("x", vm, ids_data, ap_tracking)?
        .pack86()
        .mod_floor(&SECP256R1_P);

    let y_square_int = y_squared_from_x(&x, &SECP256R1_ALPHA, &SECP256R1_B, &SECP256R1_P);
    exec_scopes.insert_value::<BigInt>("y_square_int", y_square_int.clone());

    // Calculate (prime + 1) // 4
    let exp = (SECP256R1_P.to_owned() + BigInt::one()).div_floor(&BigInt::from(4));
    // Calculate pow(y_square_int, exp, prime)
    let y = y_square_int.modpow(&exp, &SECP256R1_P);
    exec_scopes.insert_value::<BigInt>("y", y.clone());

    let v = get_integer_from_var_name("v", vm, ids_data, ap_tracking)?.to_biguint();
    if v.is_even() == y.is_even() {
        exec_scopes.insert_value("value", y);
    } else {
        let value = (-y).mod_floor(&SECP256R1_P);
        exec_scopes.insert_value("value", value);
    }
    Ok(())
}

pub const IS_ON_CURVE_2: &str = r#"ids.is_on_curve = (y * y) % SECP256R1.prime == y_square_int"#;

pub fn is_on_curve_2(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let y: BigInt = exec_scopes.get("y")?;
    let y_square_int: BigInt = exec_scopes.get("y_square_int")?;

    let is_on_curve = ((y.pow(2)) % SECP256R1_P.to_owned()) == y_square_int;
    insert_value_from_var_name(
        "is_on_curve",
        Felt252::from(is_on_curve),
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

pub const SECP_DOUBLE_ASSIGN_NEW_X: &str = r#"from starkware.cairo.common.cairo_secp.secp256r1_utils import SECP256R1_P
from starkware.cairo.common.cairo_secp.secp_utils import pack

slope = pack(ids.slope, SECP256R1_P)
x = pack(ids.point.x, SECP256R1_P)
y = pack(ids.point.y, SECP256R1_P)

value = new_x = (pow(slope, 2, SECP256R1_P) - 2 * x) % SECP256R1_P"#;

pub fn double_assign_new_x(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    exec_scopes.insert_value::<BigInt>("SECP256R1_P", SECP256R1_P.clone());
    //ids.slope
    let slope = BigInt3::from_var_name("slope", vm, ids_data, ap_tracking)?;
    //ids.point
    let point = EcPoint::from_var_name("point", vm, ids_data, ap_tracking)?;

    let slope = slope.pack86().mod_floor(&SECP256R1_P);
    let x = point.x.pack86().mod_floor(&SECP256R1_P);
    let y = point.y.pack86().mod_floor(&SECP256R1_P);

    let value =
        (slope.modpow(&(2usize.into()), &SECP256R1_P) - (&x << 1u32)).mod_floor(&SECP256R1_P);

    //Assign variables to vm scope
    exec_scopes.insert_value("slope", slope);
    exec_scopes.insert_value("x", x);
    exec_scopes.insert_value("y", y);
    exec_scopes.insert_value("value", value.clone());
    exec_scopes.insert_value("new_x", value);
    Ok(())
}

pub const GENERATE_NIBBLES: &str = r#"num = (ids.scalar.high << 128) + ids.scalar.low
nibbles = [(num >> i) & 0xf for i in range(0, 256, 4)]
ids.first_nibble = nibbles.pop()
ids.last_nibble = nibbles[0]"#;
pub fn generate_nibbles(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let num = Uint256::from_var_name("scalar", vm, ids_data, ap_tracking)?.pack();

    // Generate nibbles
    let mut nibbles: Vec<Felt252> = (0..256)
        .step_by(4)
        .map(|i| ((&num >> i) & BigUint::from_u8(0xf).unwrap()))
        .map(|s: BigUint| s.into())
        .collect();

    // ids.first_nibble = nibbles.pop()
    let first_nibble = nibbles.pop().unwrap();

    insert_value_from_var_name("first_nibble", first_nibble, vm, ids_data, ap_tracking)?;

    // ids.last_nibble = nibbles[0]
    let last_nibble = *nibbles.get(0).unwrap();
    insert_value_from_var_name("last_nibble", last_nibble, vm, ids_data, ap_tracking)?;
    exec_scopes.insert_value("nibbles", nibbles);
    Ok(())
}

pub const FAST_SECP_ADD_ASSIGN_NEW_Y: &str =
    r#"value = new_y = (slope * (x - new_x) - y) % SECP256R1_P"#;
pub fn fast_secp_add_assign_new_y(
    _vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    _ids_data: &HashMap<String, HintReference>,
    _ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    //Get variables from vm scope
    let (slope, x, new_x, y, secp_p) = (
        exec_scopes.get::<BigInt>("slope")?,
        exec_scopes.get::<BigInt>("x")?,
        exec_scopes.get::<BigInt>("new_x")?,
        exec_scopes.get::<BigInt>("y")?,
        SECP256R1_P.deref(),
    );
    let value = (slope * (x - new_x) - y).mod_floor(secp_p);
    exec_scopes.insert_value("value", value.clone());
    exec_scopes.insert_value("new_y", value);

    Ok(())
}

pub const WRITE_NIBBLES_TO_MEM: &str = r#"memory[fp + 0] = to_felt_or_relocatable(nibbles.pop())"#;

pub fn write_nibbles_to_mem(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    _ids_data: &HashMap<String, HintReference>,
    _ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let nibbles: &mut Vec<Felt252> = exec_scopes.get_mut_list_ref("nibbles")?;
    let nibble = nibbles.pop().unwrap();
    vm.insert_value((vm.get_fp() + 0)?, nibble)?;

    Ok(())
}

pub const COMPUTE_VALUE_DIV_MOD: &str = r#"from starkware.python.math_utils import div_mod

value = div_mod(1, x, SECP256R1_P)"#;
pub fn compute_value_div_mod(
    _vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    _ids_data: &HashMap<String, HintReference>,
    _ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    //Get variables from vm scope
    let x = exec_scopes.get_ref::<BigInt>("x")?;

    let value = div_mod(&BigInt::one(), x, &SECP256R1_P)?;
    exec_scopes.insert_value("value", value);

    Ok(())
}

pub const WRITE_DIVMOD_SEGMENT: &str = r#"from starkware.starknet.core.os.data_availability.bls_utils import BLS_PRIME, pack, split

a = pack(ids.a, PRIME)
b = pack(ids.b, PRIME)

q, r = divmod(a * b, BLS_PRIME)

# By the assumption: |a|, |b| < 2**104 * ((2**86) ** 2 + 2**86 + 1) < 2**276.001.
# Therefore |q| <= |ab| / BLS_PRIME < 2**299.
# Hence the absolute value of the high limb of split(q) < 2**127.
segments.write_arg(ids.q.address_, split(q))
segments.write_arg(ids.res.address_, split(r))"#;

pub fn write_div_mod_segment(
    vm: &mut VirtualMachine,
    _exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let a = bls_pack(
        &BigInt3::from_var_name("a", vm, ids_data, ap_tracking)?,
        &SECP_P,
    );
    let b = bls_pack(
        &BigInt3::from_var_name("b", vm, ids_data, ap_tracking)?,
        &SECP_P,
    );
    let (q, r) = (a * b).div_mod_floor(&BLS_PRIME);
    let q_reloc = get_relocatable_from_var_name("q", vm, ids_data, ap_tracking)?;
    let res_reloc = get_relocatable_from_var_name("res", vm, ids_data, ap_tracking)?;

    let q_arg: Vec<MaybeRelocatable> = bls_split(&q)
        .into_iter()
        .map(|ref n| Felt252::from(n).into())
        .collect::<Vec<MaybeRelocatable>>();
    let res_arg: Vec<MaybeRelocatable> = bls_split(&r)
        .into_iter()
        .map(|ref n| Felt252::from(n).into())
        .collect::<Vec<MaybeRelocatable>>();
    vm.write_arg(q_reloc, &q_arg).map_err(HintError::Memory)?;
    vm.write_arg(res_reloc, &res_arg)
        .map_err(HintError::Memory)?;
    Ok(())
}

fn bls_split(num: &BigInt) -> Vec<BigInt> {
    use num_traits::Signed;
    let mut num = num.clone();
    let mut a = Vec::new();
    for _ in 0..2 {
        let residue = num.clone() % BLS_BASE.deref();
        num /= BLS_BASE.deref();
        a.push(residue);
    }
    a.push(num.clone());
    assert!(num.abs() < BigInt::from_u128(1 << 127).unwrap());
    a
}

fn as_int(value: &BigInt, prime: &BigInt) -> BigInt {
    let half_prime = prime.clone() / 2u32;
    if value > &half_prime {
        value - prime
    } else {
        value.clone()
    }
}

fn bls_pack(z: &BigInt3, prime: &BigInt) -> BigInt {
    let limbs = &z.limbs;
    limbs
        .iter()
        .enumerate()
        .fold(BigInt::zero(), |acc, (i, limb)| {
            let limb_as_int = as_int(&limb.to_bigint(), prime);
            acc + limb_as_int * &BLS_BASE.pow(i as u32)
        })
}

#[cfg(test)]
mod tests {

    use assert_matches::assert_matches;

    use crate::utils::test_utils::*;

    use super::*;

    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::*;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_is_on_curve_2() {
        let mut vm = VirtualMachine::new(false);
        vm.set_fp(1);
        let ids_data = non_continuous_ids_data![("is_on_curve", -1)];
        vm.segments = segments![((1, 0), 1)];
        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        let y = BigInt::from(1234);
        let y_square_int = y.clone() * y.clone();

        exec_scopes.insert_value("y", y);
        exec_scopes.insert_value("y_square_int", y_square_int);

        is_on_curve_2(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &Default::default(),
        )
        .expect("is_on_curve2() failed");

        let is_on_curve: Felt252 =
            get_integer_from_var_name("is_on_curve", &vm, &ids_data, &ap_tracking)
                .expect("is_on_curve2 should be put in ids_data");
        assert_eq!(is_on_curve, 1.into());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_compute_q_mod_prime() {
        let mut vm = VirtualMachine::new(false);

        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        vm.run_context.fp = 9;
        //Create hint data
        let ids_data = non_continuous_ids_data![("val", -5), ("q", 0)];
        vm.segments = segments![((1, 4), 0), ((1, 5), 0), ((1, 6), 0)];
        compute_q_mod_prime(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &Default::default(),
        )
        .expect("compute_q_mod_prime() failed");

        let q: Felt252 = get_integer_from_var_name("q", &vm, &ids_data, &ap_tracking)
            .expect("compute_q_mod_prime should have put 'q' in ids_data");
        assert_eq!(q, Felt252::from(0));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_compute_ids_high_low() {
        let mut vm = VirtualMachine::new(false);

        let value = BigInt::from(25);
        let shift = BigInt::from(12);

        vm.set_fp(14);
        let ids_data = non_continuous_ids_data![
            ("UPPER_BOUND", -14),
            ("value", -11),
            ("high", -8),
            ("low", -5),
            ("SHIFT", -2)
        ];

        vm.segments = segments!(
            //UPPER_BOUND
            ((1, 0), 18446744069414584321),
            ((1, 1), 0),
            ((1, 2), 0),
            //value
            ((1, 3), 25),
            ((1, 4), 0),
            ((1, 5), 0),
            //high
            ((1, 6), 2),
            ((1, 7), 0),
            ((1, 8), 0),
            //low
            ((1, 9), 1),
            ((1, 10), 0),
            ((1, 11), 0),
            //SHIFT
            ((1, 12), 12),
            ((1, 13), 0),
            ((1, 14), 0)
        );

        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        let constants = HashMap::from([
            (
                "UPPER_BOUND".to_string(),
                Felt252::from(18446744069414584321_u128),
            ),
            ("SHIFT".to_string(), Felt252::from(12)),
        ]);
        compute_ids_high_low(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &constants,
        )
        .expect("compute_ids_high_low() failed");

        let high: Felt252 = get_integer_from_var_name("high", &vm, &ids_data, &ap_tracking)
            .expect("compute_ids_high_low should have put 'high' in ids_data");
        let low: Felt252 = get_integer_from_var_name("low", &vm, &ids_data, &ap_tracking)
            .expect("compute_ids_high_low should have put 'low' in ids_data");

        let (expected_high, expected_low) = value.div_rem(&shift);
        assert_eq!(high, Felt252::from(expected_high));
        assert_eq!(low, Felt252::from(expected_low));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_calculate_value() {
        let mut vm = VirtualMachine::new(false);
        vm.set_fp(10);

        let ids_data = non_continuous_ids_data![("x", -10), ("v", -7)];
        vm.segments = segments!(
            // X
            ((1, 0), 18446744069414584321),
            ((1, 1), 0),
            ((1, 2), 0),
            // v
            ((1, 3), 1),
            ((1, 4), 0),
            ((1, 5), 0),
        );
        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        let x = BigInt::from(18446744069414584321u128); // Example x value
        let v = BigInt::from(1); // Example v value (must be 0 or 1 for even/odd check)

        let constants = HashMap::new();

        r1_get_point_from_x(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &constants,
        )
        .expect("calculate_value() failed");

        let value: BigInt = exec_scopes
            .get("value")
            .expect("value should be calculated and stored in exec_scopes");

        // Compute y_squared_from_x(x)
        let y_square_int = (x.modpow(&BigInt::from(3), &SECP256R1_P)
            + SECP256R1_ALPHA.deref() * &x
            + SECP256R1_B.deref())
        .mod_floor(&SECP256R1_P);

        // Calculate y = pow(y_square_int, (SECP256R1_P + 1) // 4, SECP256R1_P)
        let exp = (SECP256R1_P.deref() + BigInt::one()).div_floor(&BigInt::from(4));
        let y = y_square_int.modpow(&exp, &SECP256R1_P);

        // Determine the expected value based on the parity of v and y
        let expected_value = if v.is_even() == y.is_even() {
            y
        } else {
            (-y).mod_floor(&SECP256R1_P)
        };

        assert_eq!(value, expected_value);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_pack_x_prime() {
        let mut vm = VirtualMachine::new(false);

        //Initialize fp
        vm.run_context.fp = 10;

        //Create hint data
        let ids_data = non_continuous_ids_data![("x", -5)];

        vm.segments = segments![
            ((1, 5), ("132181232131231239112312312313213083892150", 10)),
            ((1, 6), 10),
            ((1, 7), 10)
        ];

        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        reduce_value(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &Default::default(),
        )
        .expect("pack_x_prime() failed");

        assert_matches!(
            exec_scopes.get::<BigInt>("value"),
            Ok(x) if x == bigint_str!(
                "59863107065205964761754162760883789350782881856141750"
            )
        );
    }
}
