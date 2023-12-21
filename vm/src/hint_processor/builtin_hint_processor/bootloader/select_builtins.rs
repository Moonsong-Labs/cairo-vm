use num_traits::ToPrimitive;
use std::any::Any;
use std::collections::HashMap;

use crate::hint_processor::builtin_hint_processor::bootloader::vars;
use crate::hint_processor::builtin_hint_processor::hint_utils::get_integer_from_var_name;
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::serde::deserialize_program::ApTracking;
use crate::types::errors::math_errors::MathError;
use crate::types::exec_scope::ExecutionScopes;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::vm_core::VirtualMachine;

/// Implements
/// %{ vm_enter_scope({'n_selected_builtins': ids.n_selected_builtins}) %}
pub fn select_builtins_enter_scope(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let n_selected_builtins =
        get_integer_from_var_name(vars::N_SELECTED_BUILTINS, vm, ids_data, ap_tracking)?
            .into_owned();
    let n_selected_builtins =
        n_selected_builtins
            .to_usize()
            .ok_or(MathError::Felt252ToUsizeConversion(Box::new(
                n_selected_builtins,
            )))?;

    exec_scopes.enter_scope(HashMap::from([(
        vars::N_SELECTED_BUILTINS.to_string(),
        Box::new(n_selected_builtins) as Box<dyn Any>,
    )]));

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::hint_processor::hint_processor_definition::HintReference;
    use crate::types::exec_scope::ExecutionScopes;
    use crate::utils::test_utils::*;
    use crate::vm::vm_core::VirtualMachine;

    use super::*;

    #[test]
    fn test_select_builtins_enter_scope() {
        let mut vm = vm!();
        // Set n_selected_builtins to 7
        vm.run_context.fp = 1;
        vm.segments = segments![((1, 0), 7)];
        let ids_data = ids_data![vars::N_SELECTED_BUILTINS];
        let n_selected_builtins = 7usize;

        let ap_tracking = ApTracking::default();
        let mut exec_scopes = ExecutionScopes::new();

        select_builtins_enter_scope(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that we entered a new scope
        assert_eq!(exec_scopes.data.len(), 2);
        assert_eq!(exec_scopes.data[1].len(), 1);

        let n_selected_builtins_var: usize = exec_scopes.get(vars::N_SELECTED_BUILTINS).unwrap();

        assert_eq!(n_selected_builtins_var, n_selected_builtins);
    }
}
