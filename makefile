CC=gcc
CFLAGS=-lm -Wall

%.o: %.c 
	$(CC) -c -o $@ $< $(CFLAGS)

hourmaze: hourmaze.o 
	$(CC) -o hourmaze hourmaze.o $(CFLAGS)

.PHONY : clean
clean : 
	-rm *.o $(objects) hourmaze