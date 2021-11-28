cmake_minimum_required(VERSION 3.21)

cmake_policy(SET CMP0064 NEW) # Support if (TEST) operator

include(CMakeDependentOption)
include(CheckCCompilerFlag)

project(mochivm LANGUAGES C)

set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED true)

cmake_dependent_option(MOCHIVM_USE_UV "Use the LibUV runtime battery." ON "USE_UV" OFF)
cmake_dependent_option(MOCHIVM_USE_SDL "Use the SDL runtime battery." ON "USE_SDL" OFF)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}")
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}")

# Compiler check
string(CONCAT is-msvc $<OR:
  $<C_COMPILER_ID:MSVC>,
  $<STREQUAL:${CMAKE_C_COMPILER_FRONTEND_VARIANT},MSVC>
>)

check_c_compiler_flag(/W4 MOCHIVM_LINT_W4)
check_c_compiler_flag(/wd4100 MOCHIVM_LINT_NO_UNUSED_PARAMETER_MSVC)
check_c_compiler_flag(/wd4127 MOCHIVM_LINT_NO_CONDITIONAL_CONSTANT_MSVC)
check_c_compiler_flag(/wd4201 MOCHIVM_LINT_NO_NONSTANDARD_MSVC)
check_c_compiler_flag(/wd4206 MOCHIVM_LINT_NO_NONSTANDARD_EMPTY_TU_MSVC)
check_c_compiler_flag(/wd4210 MOCHIVM_LINT_NO_NONSTANDARD_FILE_SCOPE_MSVC)
check_c_compiler_flag(/wd4232 MOCHIVM_LINT_NO_NONSTANDARD_NONSTATIC_DLIMPORT_MSVC)
check_c_compiler_flag(/wd4456 MOCHIVM_LINT_NO_HIDES_LOCAL)
check_c_compiler_flag(/wd4457 MOCHIVM_LINT_NO_HIDES_PARAM)
check_c_compiler_flag(/wd4459 MOCHIVM_LINT_NO_HIDES_GLOBAL)
check_c_compiler_flag(/wd4706 MOCHIVM_LINT_NO_CONDITIONAL_ASSIGNMENT_MSVC)
check_c_compiler_flag(/wd4996 MOCHIVM_LINT_NO_UNSAFE_MSVC)

check_c_compiler_flag(-Wall MOCHIVM_LINT_WALL) # DO NOT use this under MSVC

# TODO: Place these into its own function
check_c_compiler_flag(-Wno-unused-parameter MOCHIVM_LINT_NO_UNUSED_PARAMETER)
check_c_compiler_flag(-Wstrict-prototypes MOCHIVM_LINT_STRICT_PROTOTYPES)
check_c_compiler_flag(-Wextra MOCHIVM_LINT_EXTRA)

check_c_compiler_flag(/utf-8 MOCHIVM_LINT_UTF8_MSVC)

set(lint-no-unused-parameter $<$<BOOL:${MOCHIVM_LINT_NO_UNUSED_PARAMETER}>:-Wno-unused-parameter>)
set(lint-strict-prototypes $<$<BOOL:${MOCHIVM_LINT_STRICT_PROTOTYPES}>:-Wstrict-prototypes>)
set(lint-extra $<$<BOOL:${MOCHIVM_LINT_EXTRA}>:-Wextra>)
set(lint-w4 $<$<BOOL:${MOCHIVM_LINT_W4}>:/W4>)
set(lint-no-unused-parameter-msvc $<$<BOOL:${MOCHIVM_LINT_NO_UNUSED_PARAMETER_MSVC}>:/wd4100>)
set(lint-no-conditional-constant-msvc $<$<BOOL:${MOCHIVM_LINT_NO_CONDITIONAL_CONSTANT_MSVC}>:/wd4127>)
set(lint-no-nonstandard-msvc $<$<BOOL:${MOCHIVM_LINT_NO_NONSTANDARD_MSVC}>:/wd4201>)
set(lint-no-nonstandard-empty-tu-msvc $<$<BOOL:${MOCHIVM_LINT_NO_NONSTANDARD_EMPTY_TU_MSVC}>:/wd4206>)
set(lint-no-nonstandard-file-scope-msvc $<$<BOOL:${MOCHIVM_LINT_NO_NONSTANDARD_FILE_SCOPE_MSVC}>:/wd4210>)
set(lint-no-nonstandard-nonstatic-dlimport-msvc $<$<BOOL:${MOCHIVM_LINT_NO_NONSTANDARD_NONSTATIC_DLIMPORT_MSVC}>:/wd4232>)
set(lint-no-hides-local-msvc $<$<BOOL:${MOCHIVM_LINT_NO_HIDES_LOCAL}>:/wd4456>)
set(lint-no-hides-param-msvc $<$<BOOL:${MOCHIVM_LINT_NO_HIDES_PARAM}>:/wd4457>)
set(lint-no-hides-global-msvc $<$<BOOL:${MOCHIVM_LINT_NO_HIDES_GLOBAL}>:/wd4459>)
set(lint-no-conditional-assignment-msvc $<$<BOOL:${MOCHIVM_LINT_NO_CONDITIONAL_ASSIGNMENT_MSVC}>:/wd4706>)
set(lint-no-unsafe-msvc $<$<BOOL:${MOCHIVM_LINT_NO_UNSAFE_MSVC}>:/wd4996>)
# Unfortunately, this one is complicated because MSVC and clang-cl support -Wall
# but using it is like calling -Weverything
string(CONCAT lint-default $<
  $<AND:$<BOOL:${MOCHIVM_LINT_WALL}>,$<NOT:${is-msvc}>>:-Wall
>)
set(lint-utf8-msvc $<$<BOOL:${MOCHIVM_LINT_UTF8_MSVC}>:/utf-8>)

list(APPEND mochivm_cflags ${lint-strict-prototypes} ${lint-extra} ${lint-default} ${lint-w4})
list(APPEND mochivm_cflags ${lint-no-unused-parameter})
list(APPEND mochivm_cflags ${lint-no-unused-parameter-msvc})
list(APPEND mochivm_cflags ${lint-no-conditional-constant-msvc})
list(APPEND mochivm_cflags ${lint-no-nonstandard-msvc})
list(APPEND mochivm_cflags ${lint-no-nonstandard-empty-tu-msvc})
list(APPEND mochivm_cflags ${lint-no-nonstandard-file-scope-msvc})
list(APPEND mochivm_cflags ${lint-no-nonstandard-nonstatic-dlimport-msvc})
list(APPEND mochivm_cflags ${lint-no-hides-local-msvc})
list(APPEND mochivm_cflags ${lint-no-hides-param-msvc})
list(APPEND mochivm_cflags ${lint-no-hides-global-msvc})
list(APPEND mochivm_cflags ${lint-no-conditional-assignment-msvc})
list(APPEND mochivm_cflags ${lint-no-unsafe-msvc})
list(APPEND mochivm_cflags ${lint-utf8-msvc} )

check_c_compiler_flag(-fno-strict-aliasing MOCHIVM_F_STRICT_ALIASING)
list(APPEND mochivm_cflags $<$<BOOL:${MOCHIVM_F_STRICT_ALIASING}>:-fno-strict-aliasing>)

set(mochivm_sources
    src/debug.c
    src/memory.c
    src/object.c
    src/value.c
    src/vm_interpreter.c
    src/vm.c)

if(MOCHIVM_USE_UV)
    list(APPEND mochivm_defines MOCHIVM_BATTERY_UV=1)
    list(APPEND mochivm_sources src/battery_uv.c)
    list(APPEND mochivm_libraries uv pthread dl)
else()
    list(APPEND mochivm_defines MOCHIVM_BATTERY_UV=0)
endif()

if(MOCHIVM_USE_SDL)
    list(APPEND mochivm_defines MOCHIVM_BATTERY_SDL=1)
    list(APPEND mochivm_sources src/battery_sdl.c)
    list(APPEND mochivm_libraries ${SDL2_LIBRARIES})
    find_package(SDL2 REQUIRED)
    include_directories(${SDL2_INCLUDE_DIRS})
else()
    list(APPEND mochivm_defines MOCHIVM_BATTERY_SDL=0)
endif()

add_library(mochivm SHARED ${mochivm_sources})
target_compile_definitions(mochivm
  INTERFACE
    USING_MOCHIVM_SHARED=1
  PRIVATE
    BUILDING_MOCHIVM_SHARED=1
    ${mochivm_defines})
target_compile_options(mochivm PRIVATE ${mochivm_cflags})
target_include_directories(mochivm
  PUBLIC
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
  PRIVATE
    $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/src>)
target_link_libraries(mochivm ${mochivm_libraries})

add_library(mochivm_a STATIC ${mochivm_sources})
target_compile_definitions(mochivm_a PRIVATE ${mochivm_defines})
target_compile_options(mochivm_a PRIVATE ${mochivm_cflags})
target_include_directories(mochivm_a
  PUBLIC
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
  PRIVATE
    $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/src>)
target_link_libraries(mochivm_a ${mochivm_libraries})

if(MSVC)
  set(CMAKE_DEBUG_POSTFIX d)
endif()

message(STATUS "summary of build options:
    Install prefix:  ${CMAKE_INSTALL_PREFIX}
    Target system:   ${CMAKE_SYSTEM_NAME}
    Libraries:       ${mochivm_libraries}
    Compiler:
      C compiler:    ${CMAKE_C_COMPILER} (${CMAKE_C_COMPILER_ID})
      CFLAGS:        ${CMAKE_C_FLAGS_${_build_type}} ${CMAKE_C_FLAGS}
")