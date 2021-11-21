#ifndef mochivm_battery_sdl_h
#define mochivm_battery_sdl_h

#include "mochivm.h"

// Initialize the SDL library.
// See https://wiki.libsdl.org/SDL_Init
//     a... I32 --> a... I32
void sdlmochiInit(MochiVM* vm, ObjFiber* fiber);
// Create a window with the specified position, dimensions, and flags.
// See https://wiki.libsdl.org/SDL_CreateWindow
//     a... U32 I32 I32 I32 I32 String -> a... SdlWindow
void sdlmochiCreateWindow(MochiVM* vm, ObjFiber* fiber);
// Retrieve a message about the last error that occurred on the current thread.
// See https://wiki.libsdl.org/SDL_GetError
//     a... --> a... String
void sdlmochiGetError(MochiVM* vm, ObjFiber* fiber);
// Clean up all initialized subsystems.
// See https://wiki.libsdl.org/SDL_Quit
//     a... --> a...
void sdlmochiQuit(MochiVM* vm, ObjFiber* fiber);

#endif