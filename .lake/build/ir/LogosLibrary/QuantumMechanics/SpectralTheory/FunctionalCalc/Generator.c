// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Generator
// Imports: Init LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Algebraic
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
LEAN_EXPORT lean_object* l_FunctionalCalculus_identityFunction(lean_object*);
lean_object* l_Complex_ofReal(lean_object*);
LEAN_EXPORT lean_object* l_FunctionalCalculus_identityFunction(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Complex_ofReal(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_FunctionalCalc_Algebraic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_FunctionalCalc_Generator(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_SpectralTheory_FunctionalCalc_Algebraic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
