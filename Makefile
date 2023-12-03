# Define the compiler and compiler flags.
CC = riscv64-linux-gnu-gcc
CFLAGS = -O3 -static
TARGET = sha256

$(TARGET).o: sha256.c sha256.h
	$(CC) $(CFLAGS) -c -o $@ $<

test: sha256.c sha256.h
	$(CC) $(CFLAGS) -o $(TARGET) -DSHA256_SELF_TEST__ $<

all: test $(TARGET)

clean:
	rm -f $(TARGET) *.o
