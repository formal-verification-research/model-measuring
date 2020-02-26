byte select = 3;

byte count = 0;

active proctype selecter()
{
	do
	:: select = 1;
	:: select = 2;
	:: if
		::select == 1 -> count = count+1
	::fi
	od;
}

