#include "common.h"

#if MOCHIVM_BATTERY_SDL

#include "battery_sdl.h"
#include "debug.h"
#include "memory.h"
#include <SDL.h>

void sdlmochiInit(MochiVM* vm, ObjFiber* fiber) {
    int subsystems = AS_I32(mochiFiberPopValue(fiber));
    int result = SDL_Init(subsystems);
    mochiFiberPushValue(fiber, I32_VAL(vm, result));
}

void sdlmochiCreateWindow(MochiVM* vm, ObjFiber* fiber) {
    const char* title = AS_CSTRING(mochiFiberPeekValue(fiber, 1));
    int x = AS_I32(mochiFiberPeekValue(fiber, 2));
    int y = AS_I32(mochiFiberPeekValue(fiber, 3));
    int w = AS_I32(mochiFiberPeekValue(fiber, 4));
    int h = AS_I32(mochiFiberPeekValue(fiber, 5));
    uint32_t flags = AS_U32(mochiFiberPeekValue(fiber, 6));

    SDL_Window* win = SDL_CreateWindow(title, x, y, w, h, flags);
    ASSERT(false, "sdlmochiCreateWindow currently does not function safely, needs refactor on return type.");
    ObjCPointer* ptr = mochiNewCPointer(vm, win);

    mochiFiberDropValues(fiber, 6);
    mochiFiberPushValue(fiber, OBJ_VAL(ptr));
}

void sdlmochiGetError(MochiVM* vm, ObjFiber* fiber) {
    const char* err = SDL_GetError();

    ObjByteArray* str = mochiByteArrayNil(vm);
    mochiFiberPushRoot(fiber, (Obj*)str);

    const char* c = err;
    while (*c != '\0') {
        mochiByteArraySnoc(vm, *c, str);
        c += 1;
    }
    mochiByteArraySnoc(vm, '\0', str);

    mochiFiberPopRoot(fiber);
    mochiFiberPushValue(fiber, OBJ_VAL(str));
}

void sdlmochiQuit(MochiVM* vm, ObjFiber* fiber) {
    SDL_Quit();
}

#endif