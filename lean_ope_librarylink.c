#include <lean/lean.h>
#include <string.h>
#include <WolframLibrary.h>

LEAN_EXPORT lean_object *initialize_StringCodeLean_StringCodeLean_LeanOPEBridge(uint8_t builtin);
LEAN_EXPORT lean_object *lean_ope_case(lean_object *case_name);
LEAN_EXPORT lean_object *lean_ope_bench_n(lean_object *n_text);
LEAN_EXPORT void lean_initialize_runtime_module(void);

static int g_initialized = 0;

DLLEXPORT mint WolframLibrary_getVersion(void) {
  return WolframLibraryVersion;
}

DLLEXPORT int WolframLibrary_initialize(WolframLibraryData libData) {
  (void)libData;
  if (g_initialized) {
    return LIBRARY_NO_ERROR;
  }

  lean_initialize_runtime_module();
  lean_set_panic_messages(false);

  lean_object *res = initialize_StringCodeLean_StringCodeLean_LeanOPEBridge(1);
  if (lean_io_result_is_error(res)) {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return LIBRARY_FUNCTION_ERROR;
  }
  lean_dec_ref(res);

  lean_set_panic_messages(true);
  lean_io_mark_end_initialization();
  lean_init_task_manager();
  g_initialized = 1;
  return LIBRARY_NO_ERROR;
}

DLLEXPORT void WolframLibrary_uninitialize(WolframLibraryData libData) {
  (void)libData;
  if (g_initialized) {
    lean_finalize_task_manager();
    g_initialized = 0;
  }
}

DLLEXPORT int leanOPECaseLL(WolframLibraryData libData, mint argc, MArgument *args, MArgument res) {
  if (!g_initialized || argc != 1) {
    return LIBRARY_FUNCTION_ERROR;
  }

  char *case_name = MArgument_getUTF8String(args[0]);
  lean_object *in = lean_mk_string(case_name);
  lean_object *out_obj = lean_ope_case(in);
  const char *out_cstr = lean_string_cstr(out_obj);

  size_t out_len = strlen(out_cstr);
  char *out = (char *)libData->WL_malloc(out_len + 1);
  if (out == NULL) {
    lean_dec(out_obj);
    libData->UTF8String_disown(case_name);
    return LIBRARY_MEMORY_ERROR;
  }

  memcpy(out, out_cstr, out_len + 1);
  MArgument_setUTF8String(res, out);

  lean_dec(out_obj);
  libData->UTF8String_disown(case_name);
  return LIBRARY_NO_ERROR;
}

DLLEXPORT int leanOPEBenchNLL(WolframLibraryData libData, mint argc, MArgument *args, MArgument res) {
  if (!g_initialized || argc != 1) {
    return LIBRARY_FUNCTION_ERROR;
  }

  char *n_text = MArgument_getUTF8String(args[0]);
  lean_object *in = lean_mk_string(n_text);
  lean_object *out_obj = lean_ope_bench_n(in);
  const char *out_cstr = lean_string_cstr(out_obj);

  size_t out_len = strlen(out_cstr);
  char *out = (char *)libData->WL_malloc(out_len + 1);
  if (out == NULL) {
    lean_dec(out_obj);
    libData->UTF8String_disown(n_text);
    return LIBRARY_MEMORY_ERROR;
  }

  memcpy(out, out_cstr, out_len + 1);
  MArgument_setUTF8String(res, out);

  lean_dec(out_obj);
  libData->UTF8String_disown(n_text);
  return LIBRARY_NO_ERROR;
}
