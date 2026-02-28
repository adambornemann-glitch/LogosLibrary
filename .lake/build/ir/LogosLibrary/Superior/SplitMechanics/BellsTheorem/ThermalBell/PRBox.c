// Lean compiler output
// Module: LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.PRBox
// Imports: Init LogosLibrary.Superior.SplitMechanics.BellsTheorem.TLHV
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
static lean_object* l_ThermalBell_CHSH__algebraic__max___closed__0;
lean_object* l_Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___ENat_toENNReal_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_CHSH__algebraic__max;
static lean_object* _init_l_ThermalBell_CHSH__algebraic__max___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___ENat_toENNReal_spec__0_spec__0_spec__0_spec__0_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_l_ThermalBell_CHSH__algebraic__max() {
_start:
{
lean_object* x_1; 
x_1 = l_ThermalBell_CHSH__algebraic__max___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_TLHV(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_PRBox(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_TLHV(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ThermalBell_CHSH__algebraic__max___closed__0 = _init_l_ThermalBell_CHSH__algebraic__max___closed__0();
lean_mark_persistent(l_ThermalBell_CHSH__algebraic__max___closed__0);
l_ThermalBell_CHSH__algebraic__max = _init_l_ThermalBell_CHSH__algebraic__max();
lean_mark_persistent(l_ThermalBell_CHSH__algebraic__max);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
