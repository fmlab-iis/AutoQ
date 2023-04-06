#ifndef _UTIL_SIM_H_
#define _UTIL_SIM_H_

#include <iostream>

/* function */
extern void full_adder_plus_1(int length, int *reg);
extern void full_adder_plus_1_start(int length, int *reg, int start);
extern void full_adder_plus_1_measure(int length, int *reg, int *order);
extern int int_array_full_check(int length, int *reg);
extern size_t getPeakRSS();
extern size_t getCurrentRSS();

#endif
