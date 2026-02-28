// Lean compiler output
// Module: LogosLibrary.Superior.YangMills.HopfFibration
// Imports: Init Mathlib.Algebra.Quaternion Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic Mathlib.Tactic LogosLibrary.Superior.Strings.Quaternion LogosLibrary.Superior.YangMills.DivisionAlgebra
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_toCtorIdx(uint8_t);
static lean_object* l_HopfFibration_NDA_x27_hopfTriple___closed__5;
static lean_object* l_HopfFibration_NDA_x27_hopfTriple___closed__2;
static lean_object* l_HopfFibration_NDA_x27_hopfTriple___closed__1;
LEAN_EXPORT lean_object* l_HopfFibration_extraFiberDims(uint8_t);
LEAN_EXPORT lean_object* l_HopfFibration_instDecidableEqNDA_x27___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_HopfFibration_NDA_x27_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_hopfTriple(uint8_t);
LEAN_EXPORT uint8_t l_HopfFibration_instDecidableEqNDA_x27(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_HopfFibration_qConj(lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HopfFibration_NDA_x27_hopfTriple___closed__0;
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_hopfTriple___boxed(lean_object*);
lean_object* l_Nat_cast___at___Nat_cast___at___Nat_cast___at___SuperiorString_Topology_hopfMap_u2081_spec__0_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___redArg(uint8_t, uint8_t);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_654_(lean_object*, lean_object*, lean_object*);
static lean_object* l_HopfFibration_NDA_x27_hopfTriple___closed__6;
LEAN_EXPORT lean_object* l_HopfFibration_realHopf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HopfFibration_NDA_x27_hopfTriple___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_npowRec___at___SuperiorString_Topology_hopfMap_u2083_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_HopfFibration_NDA_x27_hopfTriple___closed__3;
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_toCtorIdx___boxed(lean_object*);
static lean_object* l_HopfFibration_NDA_x27_hopfTriple___closed__7;
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___redArg___lam__0(lean_object*);
static lean_object* l_HopfFibration_realHopf___closed__0;
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_extraFiberDims___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HopfFibration_qConj(lean_object* x_1) {
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
static lean_object* _init_l_HopfFibration_realHopf___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at___Nat_cast___at___Nat_cast___at___SuperiorString_Topology_hopfMap_u2081_spec__0_spec__0_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_realHopf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_unsigned_to_nat(2u);
lean_inc(x_1);
x_4 = l_npowRec___at___SuperiorString_Topology_hopfMap_u2083_spec__0(x_3, x_1);
lean_inc(x_2);
x_5 = l_npowRec___at___SuperiorString_Topology_hopfMap_u2083_spec__0(x_3, x_2);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_6);
x_8 = l_HopfFibration_realHopf___closed__0;
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
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_HopfFibration_NDA_x27_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_HopfFibration_NDA_x27_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HopfFibration_NDA_x27_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HopfFibration_NDA_x27_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_HopfFibration_NDA_x27_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_HopfFibration_NDA_x27_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_HopfFibration_NDA_x27_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_1, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 3;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 2;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_HopfFibration_NDA_x27_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_HopfFibration_instDecidableEqNDA_x27(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_HopfFibration_NDA_x27_toCtorIdx(x_1);
x_4 = l_HopfFibration_NDA_x27_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_instDecidableEqNDA_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_HopfFibration_instDecidableEqNDA_x27(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_HopfFibration_NDA_x27_hopfTriple___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_HopfFibration_NDA_x27_hopfTriple___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HopfFibration_NDA_x27_hopfTriple___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_HopfFibration_NDA_x27_hopfTriple___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_HopfFibration_NDA_x27_hopfTriple___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HopfFibration_NDA_x27_hopfTriple___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_HopfFibration_NDA_x27_hopfTriple___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_HopfFibration_NDA_x27_hopfTriple___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HopfFibration_NDA_x27_hopfTriple___closed__4;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_HopfFibration_NDA_x27_hopfTriple___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_HopfFibration_NDA_x27_hopfTriple___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HopfFibration_NDA_x27_hopfTriple___closed__6;
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_hopfTriple(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_HopfFibration_NDA_x27_hopfTriple___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_HopfFibration_NDA_x27_hopfTriple___closed__3;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_HopfFibration_NDA_x27_hopfTriple___closed__5;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l_HopfFibration_NDA_x27_hopfTriple___closed__7;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_HopfFibration_NDA_x27_hopfTriple___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_HopfFibration_NDA_x27_hopfTriple(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_1) {
case 0:
{
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_inc(x_3);
return x_3;
}
case 2:
{
lean_inc(x_4);
return x_4;
}
default: 
{
lean_inc(x_5);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_2) {
case 0:
{
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_inc(x_4);
return x_4;
}
case 2:
{
lean_inc(x_5);
return x_5;
}
default: 
{
lean_inc(x_6);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l___private_LogosLibrary_Superior_YangMills_HopfFibration_0__HopfFibration_NDA_x27_hopfTriple_match__1_splitter(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_extraFiberDims(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_HopfFibration_NDA_x27_hopfTriple(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HopfFibration_extraFiberDims___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_HopfFibration_extraFiberDims(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Quaternion(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_Strings_Quaternion(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_YangMills_DivisionAlgebra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_YangMills_HopfFibration(uint8_t builtin, lean_object* w) {
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
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_Strings_Quaternion(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_YangMills_DivisionAlgebra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HopfFibration_realHopf___closed__0 = _init_l_HopfFibration_realHopf___closed__0();
lean_mark_persistent(l_HopfFibration_realHopf___closed__0);
l_HopfFibration_NDA_x27_hopfTriple___closed__0 = _init_l_HopfFibration_NDA_x27_hopfTriple___closed__0();
lean_mark_persistent(l_HopfFibration_NDA_x27_hopfTriple___closed__0);
l_HopfFibration_NDA_x27_hopfTriple___closed__1 = _init_l_HopfFibration_NDA_x27_hopfTriple___closed__1();
lean_mark_persistent(l_HopfFibration_NDA_x27_hopfTriple___closed__1);
l_HopfFibration_NDA_x27_hopfTriple___closed__2 = _init_l_HopfFibration_NDA_x27_hopfTriple___closed__2();
lean_mark_persistent(l_HopfFibration_NDA_x27_hopfTriple___closed__2);
l_HopfFibration_NDA_x27_hopfTriple___closed__3 = _init_l_HopfFibration_NDA_x27_hopfTriple___closed__3();
lean_mark_persistent(l_HopfFibration_NDA_x27_hopfTriple___closed__3);
l_HopfFibration_NDA_x27_hopfTriple___closed__4 = _init_l_HopfFibration_NDA_x27_hopfTriple___closed__4();
lean_mark_persistent(l_HopfFibration_NDA_x27_hopfTriple___closed__4);
l_HopfFibration_NDA_x27_hopfTriple___closed__5 = _init_l_HopfFibration_NDA_x27_hopfTriple___closed__5();
lean_mark_persistent(l_HopfFibration_NDA_x27_hopfTriple___closed__5);
l_HopfFibration_NDA_x27_hopfTriple___closed__6 = _init_l_HopfFibration_NDA_x27_hopfTriple___closed__6();
lean_mark_persistent(l_HopfFibration_NDA_x27_hopfTriple___closed__6);
l_HopfFibration_NDA_x27_hopfTriple___closed__7 = _init_l_HopfFibration_NDA_x27_hopfTriple___closed__7();
lean_mark_persistent(l_HopfFibration_NDA_x27_hopfTriple___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
