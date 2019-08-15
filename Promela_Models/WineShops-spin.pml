#define N 3  // Shelf size
#define N2 6 // History length

// define number of instances of each process for the spins compiler
#define __instances_winery 1
#define __instances_patron 1


// Types Of Wine   //
// 1 = Shop 1 Wine //
// 2 = Show 2 Wine //

//LTL Parts
#define hasOne (wine1s >= 1)
#define hasN (wine1s >= N)
#define has2N (wine1s >= N2)

int wine1s = N2;
hidden int i = 0;
hidden byte history[N2] = 1;
byte boughtWine = 0;

// A function to aid in later readability
inline updateHistory() {
	atomic {
		i = N2 - 1;
		wine1s = 0;
		do
		:: i > 0 -> 
			history[i] = history[i - 1];
			i--
		:: else -> 
			break
		od;
		history[0] = boughtWine;
		i = N2 - 1;
		do
		:: (i >= 0) && (history[i] == 1) ->
			wine1s++;
			i--
		:: (i >= 0) && (history[i] != 1) ->
			i--
		:: else ->
			break
		od;
		i = 0;
	}
}

chan shelf1 = [N] of {byte}
chan shelf2 = [N] of {byte}

active proctype winery() {
	do
	:: shelf1!1 ->
		// use the pc pointing to this next instruction
		// to label the previous action
		_ = 0
	:: shelf2!2 ->
		_ = 0
	od;
}

active proctype patron() {
	do
	:: if
	   :: !(shelf1?[boughtWine]) && (shelf2?[boughtWine]) -> 
	   	shelf2?boughtWine;
		updateHistory()
	   :: shelf1?[boughtWine] ->
		shelf1?boughtWine;
		updateHistory()
	   fi
	od;
}

ltl alwaysOne {[] hasOne}
ltl alwaysN {[] hasN}
ltl always2N {[] has2N}
