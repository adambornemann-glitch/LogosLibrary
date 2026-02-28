// Lean compiler output
// Module: LogosLibrary.Superior.Bridges.Knots.HopfTowerKnot
// Imports: Init Mathlib.Algebra.Quaternion Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Analysis.SpecialFunctions.Sqrt Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HopfTowerKnot_knotII__data;
LEAN_EXPORT lean_object* l_HopfTowerKnot_embed_u03b2(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfTowerKnot_knotI__data;
lean_object* l_Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___ENat_toENNReal_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*);
static lean_object* l_HopfTowerKnot_knotII__data___closed__0;
LEAN_EXPORT lean_object* l_HopfTowerKnot_realHopf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfTowerKnot_fueterSymbol(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HopfTowerKnot_knotII__data___closed__1;
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_345_;
static lean_object* l_HopfTowerKnot_knotI__data___closed__1;
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfTowerKnot_hopfMap_u2082(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfTowerKnot_hopfMap_u2083(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfTowerKnot_embedReal(lean_object*);
LEAN_EXPORT lean_object* l_HopfTowerKnot_hopfMap_u2081(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___HopfTowerKnot_realHopf_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_HopfTowerKnot_fueterConjSymbol(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HopfTowerKnot_hopfMap_u2081___closed__0;
LEAN_EXPORT lean_object* l_HopfTowerKnot_qConj(lean_object*);
lean_object* l_npowRec___at___Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfTowerKnot_embed_u03b1(lean_object*, lean_object*);
static lean_object* l_HopfTowerKnot_knotI__data___closed__2;
static lean_object* l_HopfTowerKnot_knotI__data___closed__0;
LEAN_EXPORT lean_object* l_Nat_cast___at___HopfTowerKnot_realHopf_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___ENat_toENNReal_spec__0_spec__0_spec__0_spec__0_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_realHopf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_unsigned_to_nat(2u);
lean_inc(x_1);
x_4 = l_npowRec___at___Cardinal_cantorFunctionAux_spec__0(x_3, x_1);
lean_inc(x_2);
x_5 = l_npowRec___at___Cardinal_cantorFunctionAux_spec__0(x_3, x_2);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Nat_cast___at___HopfTowerKnot_realHopf_spec__0(x_3);
x_9 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_HopfTowerKnot_hopfMap_u2081___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___Nat_cast___at___ENat_toENNReal_spec__0_spec__0_spec__0_spec__0_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_hopfMap_u2081(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_HopfTowerKnot_hopfMap_u2081___closed__0;
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_hopfMap_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_HopfTowerKnot_hopfMap_u2081___closed__0;
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_), 3, 2);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_hopfMap_u2083(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_npowRec___at___Cardinal_cantorFunctionAux_spec__0(x_5, x_1);
x_7 = l_npowRec___at___Cardinal_cantorFunctionAux_spec__0(x_5, x_2);
x_8 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_npowRec___at___Cardinal_cantorFunctionAux_spec__0(x_5, x_3);
x_10 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = l_npowRec___at___Cardinal_cantorFunctionAux_spec__0(x_5, x_4);
x_13 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_qConj(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_8, 0, x_5);
lean_ctor_set(x_1, 3, x_8);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_14, 0, x_11);
x_15 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_fueterSymbol(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_fueterConjSymbol(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_embed_u03b1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_345_;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_embed_u03b2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_345_;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HopfTowerKnot_embedReal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_345_;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_HopfTowerKnot_knotI__data___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ℝ", 3, 1);
return x_1;
}
}
static lean_object* _init_l_HopfTowerKnot_knotI__data___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ℂ", 3, 1);
return x_1;
}
}
static lean_object* _init_l_HopfTowerKnot_knotI__data___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_HopfTowerKnot_knotI__data___closed__1;
x_5 = l_HopfTowerKnot_knotI__data___closed__0;
x_6 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_3);
lean_ctor_set(x_6, 5, x_1);
lean_ctor_set(x_6, 6, x_3);
lean_ctor_set(x_6, 7, x_3);
lean_ctor_set(x_6, 8, x_1);
return x_6;
}
}
static lean_object* _init_l_HopfTowerKnot_knotI__data() {
_start:
{
lean_object* x_1; 
x_1 = l_HopfTowerKnot_knotI__data___closed__2;
return x_1;
}
}
static lean_object* _init_l_HopfTowerKnot_knotII__data___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ℍ", 3, 1);
return x_1;
}
}
static lean_object* _init_l_HopfTowerKnot_knotII__data___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(7u);
x_4 = lean_unsigned_to_nat(3u);
x_5 = l_HopfTowerKnot_knotII__data___closed__0;
x_6 = l_HopfTowerKnot_knotI__data___closed__1;
x_7 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
lean_ctor_set(x_7, 6, x_2);
lean_ctor_set(x_7, 7, x_2);
lean_ctor_set(x_7, 8, x_1);
return x_7;
}
}
static lean_object* _init_l_HopfTowerKnot_knotII__data() {
_start:
{
lean_object* x_1; 
x_1 = l_HopfTowerKnot_knotII__data___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Quaternion(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Sqrt(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_Bridges_Knots_HopfTowerKnot(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Quaternion(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Sqrt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HopfTowerKnot_hopfMap_u2081___closed__0 = _init_l_HopfTowerKnot_hopfMap_u2081___closed__0();
lean_mark_persistent(l_HopfTowerKnot_hopfMap_u2081___closed__0);
l_HopfTowerKnot_knotI__data___closed__0 = _init_l_HopfTowerKnot_knotI__data___closed__0();
lean_mark_persistent(l_HopfTowerKnot_knotI__data___closed__0);
l_HopfTowerKnot_knotI__data___closed__1 = _init_l_HopfTowerKnot_knotI__data___closed__1();
lean_mark_persistent(l_HopfTowerKnot_knotI__data___closed__1);
l_HopfTowerKnot_knotI__data___closed__2 = _init_l_HopfTowerKnot_knotI__data___closed__2();
lean_mark_persistent(l_HopfTowerKnot_knotI__data___closed__2);
l_HopfTowerKnot_knotI__data = _init_l_HopfTowerKnot_knotI__data();
lean_mark_persistent(l_HopfTowerKnot_knotI__data);
l_HopfTowerKnot_knotII__data___closed__0 = _init_l_HopfTowerKnot_knotII__data___closed__0();
lean_mark_persistent(l_HopfTowerKnot_knotII__data___closed__0);
l_HopfTowerKnot_knotII__data___closed__1 = _init_l_HopfTowerKnot_knotII__data___closed__1();
lean_mark_persistent(l_HopfTowerKnot_knotII__data___closed__1);
l_HopfTowerKnot_knotII__data = _init_l_HopfTowerKnot_knotII__data();
lean_mark_persistent(l_HopfTowerKnot_knotII__data);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
