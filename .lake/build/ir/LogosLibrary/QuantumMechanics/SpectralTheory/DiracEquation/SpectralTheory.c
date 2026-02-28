// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.SpectralTheory
// Imports: Init LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.Operators
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
LEAN_EXPORT lean_object* l_SpectralTheory_electronProjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_positronProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_diracTimeEvolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_diracTimeEvolution___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_diracTimeEvolution___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_positronProjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_DiracConstants_restEnergy(lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_positronProjection___redArg(lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_electronProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_(lean_object*, lean_object*, lean_object*);
lean_object* l_npowRec___at___Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_electronProjection___redArg(lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_DiracConstants_restEnergy(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_npowRec___at___Cardinal_cantorFunctionAux_spec__0(x_4, x_2);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_electronProjection___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_apply_1(x_2, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_electronProjection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_SpectralTheory_electronProjection___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_electronProjection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_SpectralTheory_electronProjection(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_positronProjection___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_apply_1(x_2, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_positronProjection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_SpectralTheory_positronProjection___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_positronProjection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_SpectralTheory_positronProjection(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_diracTimeEvolution___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_diracTimeEvolution(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_SpectralTheory_diracTimeEvolution___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_diracTimeEvolution___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_SpectralTheory_diracTimeEvolution(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_Operators(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_SpectralTheory(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_Operators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
