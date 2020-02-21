byte count = 3;

active proctype counter()
{
	do
	:: if
	   :: (count == 1) -> 
	   	count = 3;
	   :: else ->
		count = count -1;
	   fi
	od;
}

