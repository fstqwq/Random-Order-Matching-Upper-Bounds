# Linux, GCC or Clang with C++20 and pthreads.
# nauty must be built with thread-local storage (its nautyT.a library).
NAUTY_DIR ?= /usr/local/src/nauty
BOOST_INCLUDE ?= /usr/include
CXX ?= g++
CXXFLAGS ?= -O3 -std=c++20 -pthread

solver: solver.cpp $(wildcard vendor-phmap/parallel_hashmap/*.h)
	$(CXX) $(CXXFLAGS) -DUSE_TLS -I$(NAUTY_DIR) -I$(BOOST_INCLUDE) solver.cpp $(NAUTY_DIR)/nautyT.a -o $@

.PHONY: all clean
all: solver
clean:
	rm -f solver
