#define __instances_p1 1

int i = 0;
int j = 0;

active proctype p1() {
//	d_step{
		do
		:: i = 1 -> i == 1
		:: i = 2 -> i == 2
		od;
//	}
}

//active proctype p2() {
//	do
//	:: true -> j = 1
//	:: true -> j = 2
//	od;
//}
