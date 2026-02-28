// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Correlations
// Imports: Init LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Q_CHSH_Basic
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
static lean_object* l_QuantumCHSH_A_u2081___closed__0;
lean_object* l_QuantumCHSH__u03c3__z(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_(lean_object*, lean_object*);
lean_object* l_Matrix_kroneckerMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_(lean_object*, lean_object*, lean_object*);
lean_object* l_QuantumCHSH_I_u2082(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_QuantumCHSH_A_u2080(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2;
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_(lean_object*, lean_object*, lean_object*);
lean_object* l_QuantumCHSH__u03c3_u2093(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_QuantumCHSH_A_u2080___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_QuantumCHSH_A_u2081(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1;
LEAN_EXPORT lean_object* l_QuantumCHSH_A_u2080___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_6);
lean_inc(x_7);
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_7);
x_13 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
x_14 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_15);
lean_inc(x_16);
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_16);
x_19 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_16);
x_22 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_15);
x_23 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_QuantumCHSH_A_u2080(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_QuantumCHSH_A_u2080___lam__0), 2, 0);
x_4 = lean_alloc_closure((void*)(l_QuantumCHSH__u03c3__z), 2, 0);
x_5 = lean_alloc_closure((void*)(l_QuantumCHSH_I_u2082), 2, 0);
x_6 = l_Matrix_kroneckerMap___redArg(x_3, x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_l_QuantumCHSH_A_u2081___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_QuantumCHSH_A_u2080___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_QuantumCHSH_A_u2081(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_QuantumCHSH_A_u2081___closed__0;
x_4 = lean_alloc_closure((void*)(l_QuantumCHSH__u03c3_u2093), 2, 0);
x_5 = lean_alloc_closure((void*)(l_QuantumCHSH_I_u2082), 2, 0);
x_6 = l_Matrix_kroneckerMap___redArg(x_3, x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__0;
x_2 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1;
x_2 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__0;
x_11 = lean_nat_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1;
x_13 = lean_nat_dec_eq(x_8, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_apply_6(x_7, x_1, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_14;
}
else
{
uint8_t x_15; 
lean_inc(x_9);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = lean_nat_dec_eq(x_9, x_10);
if (x_18 == 0)
{
lean_object* x_19; 
lean_ctor_set(x_1, 0, x_12);
x_19 = lean_apply_6(x_7, x_1, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_9);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_nat_dec_eq(x_20, x_10);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_20, x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2;
x_25 = lean_apply_6(x_7, x_24, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_25;
}
else
{
uint8_t x_26; 
lean_inc(x_21);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_2, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_29 = lean_nat_dec_eq(x_21, x_10);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2;
lean_ctor_set(x_2, 0, x_12);
x_31 = lean_apply_6(x_7, x_30, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_31;
}
else
{
lean_free_object(x_2);
lean_dec(x_21);
lean_dec_ref(x_7);
lean_inc(x_6);
return x_6;
}
}
else
{
uint8_t x_32; 
lean_dec(x_2);
x_32 = lean_nat_dec_eq(x_21, x_10);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_21);
x_35 = lean_apply_6(x_7, x_33, x_34, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_35;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_7);
lean_inc(x_6);
return x_6;
}
}
}
}
else
{
uint8_t x_36; 
lean_inc(x_21);
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_2, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_2, 0);
lean_dec(x_38);
x_39 = lean_nat_dec_eq(x_21, x_12);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2;
lean_ctor_set(x_2, 0, x_10);
x_41 = lean_apply_6(x_7, x_40, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_41;
}
else
{
lean_free_object(x_2);
lean_dec(x_21);
lean_dec_ref(x_7);
lean_inc(x_5);
return x_5;
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = lean_nat_dec_eq(x_21, x_12);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_10);
lean_ctor_set(x_44, 1, x_21);
x_45 = lean_apply_6(x_7, x_43, x_44, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_45;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_7);
lean_inc(x_5);
return x_5;
}
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_1);
x_46 = lean_nat_dec_eq(x_9, x_10);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_9);
x_48 = lean_apply_6(x_7, x_47, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_9);
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_ctor_get(x_2, 1);
x_51 = lean_nat_dec_eq(x_49, x_10);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = lean_nat_dec_eq(x_49, x_12);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2;
x_54 = lean_apply_6(x_7, x_53, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_54;
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_inc(x_50);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_55 = x_2;
} else {
 lean_dec_ref(x_2);
 x_55 = lean_box(0);
}
x_56 = lean_nat_dec_eq(x_50, x_10);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2;
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_12);
lean_ctor_set(x_58, 1, x_50);
x_59 = lean_apply_6(x_7, x_57, x_58, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_59;
}
else
{
lean_dec(x_55);
lean_dec(x_50);
lean_dec_ref(x_7);
lean_inc(x_6);
return x_6;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_inc(x_50);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_60 = x_2;
} else {
 lean_dec_ref(x_2);
 x_60 = lean_box(0);
}
x_61 = lean_nat_dec_eq(x_50, x_12);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2;
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_10);
lean_ctor_set(x_63, 1, x_50);
x_64 = lean_apply_6(x_7, x_62, x_63, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_64;
}
else
{
lean_dec(x_60);
lean_dec(x_50);
lean_dec_ref(x_7);
lean_inc(x_5);
return x_5;
}
}
}
}
}
}
else
{
uint8_t x_65; 
lean_inc(x_9);
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_1, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_1, 0);
lean_dec(x_67);
x_68 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1;
x_69 = lean_nat_dec_eq(x_9, x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_ctor_set(x_1, 0, x_10);
x_70 = lean_apply_6(x_7, x_1, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_free_object(x_1);
lean_dec(x_9);
x_71 = lean_ctor_get(x_2, 0);
x_72 = lean_ctor_get(x_2, 1);
x_73 = lean_nat_dec_eq(x_71, x_10);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = lean_nat_dec_eq(x_71, x_68);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3;
x_76 = lean_apply_6(x_7, x_75, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_76;
}
else
{
uint8_t x_77; 
lean_inc(x_72);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_2, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_2, 0);
lean_dec(x_79);
x_80 = lean_nat_dec_eq(x_72, x_10);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3;
lean_ctor_set(x_2, 0, x_68);
x_82 = lean_apply_6(x_7, x_81, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_82;
}
else
{
lean_free_object(x_2);
lean_dec(x_72);
lean_dec_ref(x_7);
lean_inc(x_4);
return x_4;
}
}
else
{
uint8_t x_83; 
lean_dec(x_2);
x_83 = lean_nat_dec_eq(x_72, x_10);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_68);
lean_ctor_set(x_85, 1, x_72);
x_86 = lean_apply_6(x_7, x_84, x_85, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_86;
}
else
{
lean_dec(x_72);
lean_dec_ref(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
else
{
uint8_t x_87; 
lean_inc(x_72);
x_87 = !lean_is_exclusive(x_2);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_2, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_2, 0);
lean_dec(x_89);
x_90 = lean_nat_dec_eq(x_72, x_68);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3;
lean_ctor_set(x_2, 0, x_10);
x_92 = lean_apply_6(x_7, x_91, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_92;
}
else
{
lean_free_object(x_2);
lean_dec(x_72);
lean_dec_ref(x_7);
lean_inc(x_3);
return x_3;
}
}
else
{
uint8_t x_93; 
lean_dec(x_2);
x_93 = lean_nat_dec_eq(x_72, x_68);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3;
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_10);
lean_ctor_set(x_95, 1, x_72);
x_96 = lean_apply_6(x_7, x_94, x_95, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_96;
}
else
{
lean_dec(x_72);
lean_dec_ref(x_7);
lean_inc(x_3);
return x_3;
}
}
}
}
}
else
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_1);
x_97 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1;
x_98 = lean_nat_dec_eq(x_9, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_10);
lean_ctor_set(x_99, 1, x_9);
x_100 = lean_apply_6(x_7, x_99, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_9);
x_101 = lean_ctor_get(x_2, 0);
x_102 = lean_ctor_get(x_2, 1);
x_103 = lean_nat_dec_eq(x_101, x_10);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = lean_nat_dec_eq(x_101, x_97);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3;
x_106 = lean_apply_6(x_7, x_105, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_106;
}
else
{
lean_object* x_107; uint8_t x_108; 
lean_inc(x_102);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_107 = x_2;
} else {
 lean_dec_ref(x_2);
 x_107 = lean_box(0);
}
x_108 = lean_nat_dec_eq(x_102, x_10);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3;
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_97);
lean_ctor_set(x_110, 1, x_102);
x_111 = lean_apply_6(x_7, x_109, x_110, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_111;
}
else
{
lean_dec(x_107);
lean_dec(x_102);
lean_dec_ref(x_7);
lean_inc(x_4);
return x_4;
}
}
}
else
{
lean_object* x_112; uint8_t x_113; 
lean_inc(x_102);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_112 = x_2;
} else {
 lean_dec_ref(x_2);
 x_112 = lean_box(0);
}
x_113 = lean_nat_dec_eq(x_102, x_97);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3;
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_10);
lean_ctor_set(x_115, 1, x_102);
x_116 = lean_apply_6(x_7, x_114, x_115, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_116;
}
else
{
lean_dec(x_112);
lean_dec(x_102);
lean_dec_ref(x_7);
lean_inc(x_3);
return x_3;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Q__CHSH__Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Q__CHSH__Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_QuantumCHSH_A_u2081___closed__0 = _init_l_QuantumCHSH_A_u2081___closed__0();
lean_mark_persistent(l_QuantumCHSH_A_u2081___closed__0);
l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__0 = _init_l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__0();
lean_mark_persistent(l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__0);
l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1 = _init_l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1();
lean_mark_persistent(l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__1);
l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2 = _init_l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2();
lean_mark_persistent(l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__2);
l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3 = _init_l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3();
lean_mark_persistent(l___private_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations_0__QuantumCHSH__u03c1___u03a8__minus_match__1_splitter___redArg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
