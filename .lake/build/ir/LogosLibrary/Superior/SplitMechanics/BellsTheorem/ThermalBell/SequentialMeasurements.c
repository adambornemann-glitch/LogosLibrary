// Lean compiler output
// Module: LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.SequentialMeasurements
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
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_totalEntropyAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_countSettingChanges___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_totalEntropyAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_countSettingChanges(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_totalEntropyAux_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_4);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_apply_3(x_4, x_1, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_totalEntropyAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_totalEntropyAux_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ThermalBell_countSettingChanges(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(0u);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_10, 2);
x_13 = lean_nat_dec_eq(x_11, x_12);
x_14 = l_instDecidableNot___redArg(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(0u);
x_5 = x_15;
goto block_8;
}
else
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(1u);
x_5 = x_16;
goto block_8;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_ThermalBell_countSettingChanges(x_4);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_ThermalBell_countSettingChanges___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ThermalBell_countSettingChanges(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_5);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_apply_3(x_4, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements_0__ThermalBell_totalEntropy_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_TLHV(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_TLHV(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
