# Makefile for building a single configuration of the virtual machine.
# Expects the following variables:
#
# MODE			"debug" or "release"

CFLAGS := -std=gnu99 -Wall -Wextra -Werror -Wno-unused-parameter -Isrc/ -Ideps/libuv/include/ -Itest/ -Lbuild -Lbuild/utf8proc `sdl2-config --cflags`

BUILD_TOP := build

ifeq ($(NOBATTERY), yes)
	CFLAGS += -DMOCHIVM_BATTERY_SDL=0
endif

ifeq ($(MODE), debug)
	CFLAGS += -O0 -DDEBUG -g
	BUILD_DIR := $(BUILD_TOP)/debug
else
	CFLAGS += -O3 -flto
	BUILD_DIR := $(BUILD_TOP)/release
endif

BUILD_TEST_DIR := $(BUILD_DIR)/test

# Files.
HEADERS := $(wildcard src/*.h test/*.h)
SOURCES := $(wildcard src/*.c)
TESTS := $(wildcard test/*.check)
TESTEXE := $(addprefix $(BUILD_TEST_DIR)/, $(notdir $(TESTS:.check=.txe)))
OBJECTS := $(addprefix $(BUILD_DIR)/, $(notdir $(SOURCES:.c=.o)))
LIBS := -luv_a -lutf8proc -pthread -Wl,--no-as-needed -ldl
TEST_LIBS := -lcheck -lcheck_pic -lsubunit -lm -lrt

ifeq ($(NOBATTERY), yes)
else
	LIBS += `sdl2-config --libs`
endif

# Targets ---------------------------------------------------------------------

# Link the interpreter.
$(BUILD_DIR)/mochivm: $(BUILD_DIR)/main.o $(BUILD_DIR)/libmochivm.a
	@ printf "%8s %-40s %s %s\n" $(CC) $@ "$(CFLAGS)" "$(LIBS)"
	@ mkdir -p $(BUILD_DIR)
	@ $(CC) $(CFLAGS) $^ -o $@ -L$(BUILD_DIR) -lmochivm $(LIBS)

# Link into a static library.
lib: $(OBJECTS) $(BUILD_TOP)/libuv_a.a $(BUILD_TOP)/utf8proc/libutf8proc.a
	@ ar rcs $(BUILD_DIR)/libmochivm.a $(OBJECTS)

$(BUILD_DIR)/main.o: main.c $(HEADERS)
	@ printf "%8s %-40s %s\n" $(CC) $< "$(CFLAGS)"
	@ mkdir -p $(BUILD_DIR)
	@ $(CC) -c $(C_LANG) $(CFLAGS) -o $@ $<

# Build and execute all tests.
test: $(TESTEXE)

# Build and run each test executable.
$(BUILD_TEST_DIR)/%.txe: $(BUILD_TEST_DIR)/%.o $(OBJECTS) $(BUILD_TOP)/libuv_a.a $(BUILD_TOP)/utf8proc/libutf8proc.a
	@ printf "%8s %-40s %s %s %s\n" $(CC) $@ "$(CFLAGS)" "$(LIBS)" "$(TEST_LIBS)"
	@ $(CC) $(CFLAGS) $^ -o $@ $(LIBS) $(TEST_LIBS)
	@ $@
	@ rm $@

# Build the test objects files.
$(BUILD_TEST_DIR)/%.o: $(BUILD_TEST_DIR)/%.c $(HEADERS)
	@ printf "%8s %-40s %s\n" $(CC) $< "$(CFLAGS)"
	@ $(CC) -c $(C_LANG) $(CFLAGS) -o $@ $<

# Build the test source file.
$(BUILD_TEST_DIR)/%.c: test/%.check $(HEADERS)
	@ mkdir -p $(BUILD_TEST_DIR)
	@ checkmk $< > $@

# Compile object files.
$(BUILD_DIR)/%.o: src/%.c $(HEADERS)
	@ printf "%8s %-40s %s\n" $(CC) $< "$(CFLAGS)"
	@ mkdir -p $(BUILD_DIR)
	@ $(CC) -c $(C_LANG) $(CFLAGS) -o $@ $<

# Compile libuv
$(BUILD_TOP)/libuv_a.a:
	@ printf "Building libuv\n"
	@ mkdir -p $(BUILD_TOP)
	@ (cd $(BUILD_TOP) && cmake ../deps/libuv)
	@ cmake --build $(BUILD_TOP)

# Compile utf8proc
$(BUILD_TOP)/utf8proc/libutf8proc.a:
	@ printf "Building utf8proc\n"
	@ mkdir -p $(BUILD_TOP)/utf8proc
	@ (cd $(BUILD_TOP)/utf8proc && cmake ../../deps/utf8proc)
	@ (cd $(BUILD_TOP)/utf8proc && make)

# Format source files
format:
	@ printf "Formatting source files\n"
	@ clang-format -i main.c
	@ clang-format -i $(HEADERS)
	@ clang-format -i $(SOURCES)

.PHONY: default

clean:
	@ rm -rf build

clean_test:
	@ rm -rf build/**.txe