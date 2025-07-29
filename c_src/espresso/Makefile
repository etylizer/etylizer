SRC := $(wildcard *.c)

OBJ := ${SRC:.c=.o}

TARGETDIR := ../../_build
TARGET := $(TARGETDIR)/espresso

CFLAGS = -std=c99 -D_POSIX_C_SOURCE=200809L

all: prepare $(TARGET)

prepare:
	mkdir -p $(TARGETDIR)

$(TARGET): $(OBJ)
	$(LINK.c) $(OBJ) -o $(TARGET)

clean: 
	@- $(RM) $(TARGET)
	@- $(RM) $(OBJ)
