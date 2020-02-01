# A reference for creating automaton via spot can be found at:
# https://spot.lrde.epita.fr/tut22.html

import spot
import buddy
import subprocess

# creates the dictionary which maintains the correspondance between the
# atomic propositions and the Boolean decision diagram (bdd) variables that 
# label the edges of the automaton.
bdict = spot.make_bdd_dict();

#makes an empty automaton 
buchiHypervisor = spot.make_twa_graph(bdict); 

test1 = buddy.bdd_ithvar(buchiHypervisor.register_ap("test1"))
test2 = buddy.bdd_ithvar(buchiHypervisor.register_ap("test2"))

buchiHypervisor.set_generalized_buchi(2)

buchiHypervisor.new_states(3)

buchiHypervisor.set_init_state(0)

buchiHypervisor.new_edge(0,1, test1)

print(buchiHypervisor.to_str('hoa'))

buchiHypervisor.save('buchiHypervisor.hoa')
buchiHypervisor.save('buchiHypervisor.dot','dot')

ret_code = subprocess.call(['dot', '-Tpdf', 'buchiHypervisor.dot', '-o', 'buchiHypervisor.pdf'])
if ret_code == 0:
    print('Human readable Buchi automaton saved at buchiHypervisor.pdf')
