// Lean compiler output
// Module: LogosLibrary.Superior.SplitMechanics.BellsTheorem.OtherInequalities.LeggettGarg
// Imports: Init LogosLibrary.Superior.SplitMechanics.BellsTheorem.OtherInequalities.ThermMerm
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_ThermalLeggettGarg_temporalSlots(lean_object*);
LEAN_EXPORT lean_object* l_ThermalLeggettGarg_temporalSlots___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalLeggettGarg_temporalSlots(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ThermalLeggettGarg_temporalSlots___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ThermalLeggettGarg_temporalSlots(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_OtherInequalities_ThermMerm(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_OtherInequalities_LeggettGarg(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_OtherInequalities_ThermMerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
