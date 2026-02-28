// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH
// Imports: Init LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Q_CHSH_Basic LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Correlations LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Violation LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Tsirelson
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Q__CHSH__Basic(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Violation(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Tsirelson(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Q__CHSH__Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Correlations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Violation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_BellsTheorem_QuantumCHSH_Tsirelson(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
