#define N 3  // Shelf size

// define number of instances of each process for the spins compiler
#define __instances_wnry 1
#define __instances_ptrn 1


// Types Of Wine   //
// 1 = Shop 1 Wine //
// 2 = Show 2 Wine //

byte bw;

chan s1 = [N] of {byte}

active proctype wnry() {

	do
	:: s1!1
	od;
}

active proctype ptrn() {
	do
	:: if
	   :: s1?[bw] ->
		s1?bw;
	   fi
	od;
}
