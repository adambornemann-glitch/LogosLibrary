// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.GammaTraces
// Imports: Init LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.CliffordAlgebra Mathlib.Analysis.Complex.Basic Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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
lean_object* l_Dirac_Matrices_gamma1(lean_object*, lean_object*);
static lean_object* l_Dirac_Matrices_minkowskiMetric___closed__2;
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Dirac_Matrices_minkowskiMetric___closed__1;
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_minkowskiMetric___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__0(lean_object*);
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_403_;
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_345_;
LEAN_EXPORT lean_object* l_Dirac_Matrices_minkowskiMetric(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Complex_ofReal(lean_object*);
static lean_object* l_Dirac_Matrices_gamma5___closed__0;
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_gammaAt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Dirac_Matrices_gamma3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Dirac_Matrices_minkowskiMetric___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_gammaAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Dirac_Matrices_gamma2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5(lean_object*, lean_object*);
lean_object* l_Dirac_Matrices_gamma0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Dirac_Matrices_minkowskiMetric___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_345_;
x_2 = l_Complex_ofReal(x_1);
return x_2;
}
}
static lean_object* _init_l_Dirac_Matrices_minkowskiMetric___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Dirac_Matrices_minkowskiMetric___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_403_;
x_2 = l_Complex_ofReal(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_minkowskiMetric(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Dirac_Matrices_minkowskiMetric___closed__0;
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Dirac_Matrices_minkowskiMetric___closed__1;
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Dirac_Matrices_minkowskiMetric___closed__2;
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_12, 0, x_10);
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = l_Dirac_Matrices_minkowskiMetric___closed__2;
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_minkowskiMetric___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Dirac_Matrices_minkowskiMetric(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__0(lean_object* x_1) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_cases___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Fin_cases___redArg(x_1, x_2, x_3);
x_6 = lean_apply_1(x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Dirac_Matrices_gamma5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Equiv_refl(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_3 = l_Dirac_Matrices_gamma5___closed__0;
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__0___boxed), 1, 0);
x_6 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__1___boxed), 2, 0);
x_7 = l_Dirac_Matrices_minkowskiMetric___closed__0;
lean_inc_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_5);
lean_inc_ref(x_8);
x_9 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
lean_inc_ref(x_9);
x_10 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Dirac_Matrices_minkowskiMetric___closed__2;
x_12 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_9);
x_13 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__7___boxed), 4, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_6);
x_15 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_10);
x_16 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__7___boxed), 4, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_5);
x_18 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_18, 0, x_7);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_19, 0, x_7);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_20, 0, x_7);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__7___boxed), 4, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_16);
x_22 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_8);
x_23 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_23, 0, x_7);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__2___boxed), 3, 2);
lean_closure_set(x_24, 0, x_7);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Dirac_Matrices_gamma5___lam__7___boxed), 4, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_21);
x_26 = lean_apply_3(x_4, x_25, x_1, x_2);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Dirac_Matrices_gamma5___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Dirac_Matrices_gamma5___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Dirac_Matrices_gamma5___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gamma5___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Dirac_Matrices_gamma5___lam__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Dirac_Matrices_gammaAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Dirac_Matrices_gammaAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Dirac_Matrices_gammaAt(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_nat_dec_eq(x_9, x_6);
if (x_10 == 1)
{
lean_dec(x_9);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_11, x_6);
lean_dec(x_11);
if (x_12 == 1)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces_0__Dirac_Matrices_gammaAt_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_CliffordAlgebra(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_Bochner_ContinuousLinearMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_GammaTraces(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_CliffordAlgebra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_Bochner_ContinuousLinearMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Dirac_Matrices_minkowskiMetric___closed__0 = _init_l_Dirac_Matrices_minkowskiMetric___closed__0();
lean_mark_persistent(l_Dirac_Matrices_minkowskiMetric___closed__0);
l_Dirac_Matrices_minkowskiMetric___closed__1 = _init_l_Dirac_Matrices_minkowskiMetric___closed__1();
lean_mark_persistent(l_Dirac_Matrices_minkowskiMetric___closed__1);
l_Dirac_Matrices_minkowskiMetric___closed__2 = _init_l_Dirac_Matrices_minkowskiMetric___closed__2();
lean_mark_persistent(l_Dirac_Matrices_minkowskiMetric___closed__2);
l_Dirac_Matrices_gamma5___closed__0 = _init_l_Dirac_Matrices_gamma5___closed__0();
lean_mark_persistent(l_Dirac_Matrices_gamma5___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
