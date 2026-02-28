// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.Current
// Imports: Init LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.GammaTraces Mathlib.MeasureTheory.Integral.Bochner.Basic
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
static lean_object* l_Dirac_Current_spacetimePoint___closed__0;
lean_object* l_Dirac_Matrices_gamma1(lean_object*, lean_object*);
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Current_standardGammaMatrices___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___lam__0___boxed(lean_object*);
static lean_object* l_Dirac_Current_spacetimePoint___closed__2;
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Current_standardGammaMatrices___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Dirac_Matrices_gamma3(lean_object*, lean_object*);
static lean_object* l_Dirac_Current_spacetimePoint___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint(lean_object*, lean_object*, lean_object*);
lean_object* l_Dirac_Matrices_gamma2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Current_standardGammaMatrices;
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___lam__0(lean_object*);
lean_object* l_Dirac_Matrices_gamma0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Current_standardGammaMatrices___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
x_6 = l_Dirac_Matrices_gamma0(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_nat_dec_eq(x_8, x_4);
if (x_9 == 1)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = l_Dirac_Matrices_gamma1(x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_sub(x_8, x_7);
lean_dec(x_8);
x_12 = lean_nat_dec_eq(x_11, x_4);
lean_dec(x_11);
if (x_12 == 1)
{
lean_object* x_13; 
x_13 = l_Dirac_Matrices_gamma2(x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Dirac_Matrices_gamma3(x_2, x_3);
return x_14;
}
}
}
}
}
static lean_object* _init_l_Dirac_Current_standardGammaMatrices() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Dirac_Current_standardGammaMatrices___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Dirac_Current_standardGammaMatrices___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Dirac_Current_standardGammaMatrices___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___lam__0(lean_object* x_1) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_cases___redArg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Dirac_Current_spacetimePoint___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Dirac_Current_spacetimePoint___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Dirac_Current_spacetimePoint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_alloc_closure((void*)(l_Dirac_Current_spacetimePoint___lam__0___boxed), 1, 0);
x_5 = l_Dirac_Current_spacetimePoint___closed__0;
lean_inc_ref(x_2);
x_6 = lean_apply_1(x_2, x_5);
x_7 = l_Dirac_Current_spacetimePoint___closed__1;
lean_inc_ref(x_2);
x_8 = lean_apply_1(x_2, x_7);
x_9 = l_Dirac_Current_spacetimePoint___closed__2;
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_alloc_closure((void*)(l_Dirac_Current_spacetimePoint___lam__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_4);
x_12 = lean_alloc_closure((void*)(l_Dirac_Current_spacetimePoint___lam__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Dirac_Current_spacetimePoint___lam__1___boxed), 3, 2);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Fin_cases___redArg(x_1, x_13, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Dirac_Current_spacetimePoint___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Dirac_Current_spacetimePoint___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Dirac_Current_spacetimePoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Dirac_Current_spacetimePoint(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_Bochner_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_Current(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_Bochner_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Dirac_Current_standardGammaMatrices = _init_l_Dirac_Current_standardGammaMatrices();
lean_mark_persistent(l_Dirac_Current_standardGammaMatrices);
l_Dirac_Current_spacetimePoint___closed__0 = _init_l_Dirac_Current_spacetimePoint___closed__0();
lean_mark_persistent(l_Dirac_Current_spacetimePoint___closed__0);
l_Dirac_Current_spacetimePoint___closed__1 = _init_l_Dirac_Current_spacetimePoint___closed__1();
lean_mark_persistent(l_Dirac_Current_spacetimePoint___closed__1);
l_Dirac_Current_spacetimePoint___closed__2 = _init_l_Dirac_Current_spacetimePoint___closed__2();
lean_mark_persistent(l_Dirac_Current_spacetimePoint___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
