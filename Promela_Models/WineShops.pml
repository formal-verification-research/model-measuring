#define N 3  // Shelf size
#define N2 6 // History length

// define number of instances of each process for the spins compiler
#define __instances_winery 1
#define __instances_patron 1


//TODO The postprocess method encounters either a segfault or an OOM kill with this model
//TODONE The solution was to hide the attay and use 'Low' optimization for postprocess

// Types Of Wine   //
// 0 = No Wine     //
// 1 = Shop 1 Wine //
// 2 = Show 2 Wine //

//LTL Parts (needed to make ltl checking work, not needed for buchi)
#define hasOne (wine1s >= 1)
#define hasHalfN (wine1s >= N / 2)
#define has2N (wine1s >= 2*N)

int wine1s = N2;
hidden int i = 0;
byte history[N2];
byte boughtWine = 0;

// A function to aid in later readability
inline updateHistory() {
	d_step {
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
	:: !full(shelf1) -> shelf1!1
	:: full(shelf1) && !full(shelf2) -> shelf2!2
	od;
}

active proctype patron() {
	// Wine Buying loop
	do
	:: !empty(shelf1) -> 
		shelf1?boughtWine;
		atomic {
			updateHistory();
			boughtWine = 0;
		}
	:: empty(shelf1) && !empty(shelf2) -> 
		shelf2?boughtWine;
		atomic {
			updateHistory();
			boughtWine = 0;
		}
	od;
}


// These must be commented for buchi conversion.

//# ltl alwaysOne {[] hasOne}
//# ltl eventually {<> hasOne}
//# ltl alwaysHalfN {[] hasHalfN}
//# ltl always2N {[] has2N}
