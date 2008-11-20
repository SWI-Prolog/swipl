#-----------------------------------------------------------------
# FUNCTION
#   Makefile for AES library
#
# AUTHOR
#   Keri Harris (keri.harris@securitease.com)
#
#-----------------------------------------------------------------
#   COPYRIGHT (C) 2008 SCIENTIFIC SOFTWARE AND SYSTEMS LIMITED
#
#     - REFER TO FILE LICENCE.TXT FOR FULL LICENCE DETAILS -
#-----------------------------------------------------------------

# Configuration hacks added by Matt. Don't blame Keri for these!
CC=/cygdrive/c/se_tools/mingw64-2008-09-20/bin/gcc.exe
SO=.dll
SWI=/cygdrive/c/se_tools/swi/pl-5.7.2
SWI_LIB=$(shell cygpath -m $(SWI)/lib)
SWI_INCLUDE=$(shell cygpath -m $(SWI)/include)
DELETE=rm -f



#-----------------------------------------------------------------
# AES SOURCE FILES AND OBJECT FILES
#-----------------------------------------------------------------

AES_OBJ= aes.o                                                   \
         aescrypt.o                                              \
         aeskey.o                                                \
         aestab.o

AES_SRC= aes.c                                            \
         aes.h                                            \
         aesopt.h                                         \
         $(SWI)/include/SWI-Prolog.h

AESCRYPT_SRC= aescrypt.c                                  \
              aes.h                                       \
              aestab.h                                    \
              aesopt.h

AESKEY_SRC= aeskey.c                                      \
            aes.h                                         \
            aestab.h                                      \
            aesopt.h

AESTAB_SRC= aestab.c                                      \
            aes.h                                         \
            aestab.h                                      \
            aesopt.h



#-----------------------------------------------------------------
# AES RULES
#-----------------------------------------------------------------

.PHONY: all clean


all: aes$(SO)

aes$(SO): $(AES_OBJ)
	$(CC) $(LDFLAGS) -o $@ $^ -L$(SWI_LIB) -shared -llibpl

aes.o: $(AES_SRC)
	$(CC) $(CFLAGS) -I. -I$(SWI_INCLUDE) -c -o $@ $<

aescrypt.o: $(AESCRYPT_SRC)
	$(CC) $(CFLAGS) -c -o $@ $<

aeskey.o: $(AESKEY_SRC)
	$(CC) $(CFLAGS) -c -o $@ $<

aestab.o: $(AESTAB_SRC)
	$(CC) $(CFLAGS) -c -o $@ $<

clean:
	$(DELETE) aes$(SO)
	$(DELETE) *.o
