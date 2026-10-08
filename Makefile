CC = gcc -g -Wall -pedantic

default: main

main: main.c 
	$(CC) main.c -o Parser -lcjson


clean:
	rm -f *.o main
