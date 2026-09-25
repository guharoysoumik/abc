#!/bin/bash

echo "--------------------------------------------"
echo " ABC Build Script (matching VSCode build) "
echo "--------------------------------------------"

# Detect GCC and C++ compilers
export CC=gcc
export CXX=g++
export AR=ar
export LD=g++

echo "Using CC=$CC"
echo "Using CXX=$CXX"
echo "Using AR=$AR"
echo "Using LD=$LD"

# ABC optional features (same as VSCode)
USE_CUDD=1
USE_READLINE=1
USE_PTHREADS=1

echo "Compiling with CUDD"
echo "Using libreadline"
echo "Using pthreads"

# Query GCC version
GCC_VERSION=$(gcc -dumpfullversion -dumpversion)
GCC_MAJOR=$(echo "$GCC_VERSION" | cut -d. -f1)

echo "Found GCC_VERSION $GCC_VERSION"
echo "Found GCC_MAJOR>=$GCC_MAJOR"

# These flags match ABC's makefile behavior
export CFLAGS="-Wall -Wno-unused-function -Wno-write-strings -Wno-sign-compare \
-DLIN64 -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8 -DSIZEOF_INT=4 \
-DABC_USE_CUDD=${USE_CUDD} -DABC_USE_READLINE=${USE_READLINE} \
-DABC_USE_PTHREADS=${USE_PTHREADS} -Wno-unused-but-set-variable"

echo "Using CFLAGS=$CFLAGS"

echo ""
echo "========== BEGIN ABC BUILD =========="
echo ""

# Run make
make -j$(nproc)

STATUS=$?

echo ""
echo "========== BUILD COMPLETE =========="
echo "Exit Status: $STATUS"
echo "Binary expected at: ./abc"
echo "[By SGR]"

exit $STATUS
