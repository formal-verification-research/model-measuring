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

true = buddy.bdd_ithvar(buchiHypervisor.register_ap("true"))
label = buddy.bdd_ithvar(buchiHypervisor.register_ap("ltl"))
notLabel = buddy.bdd_ithvar(buchiHypervisor.register_ap("!ltl"))
transitionLabel = buddy.bdd_ithvar(buchiHypervisor.register_ap("transition"))

buchiHypervisor.set_generalized_buchi(2)

buchiHypervisor.new_states(2)

buchiHypervisor.set_init_state(0)

buchiHypervisor.new_edge(0,0, t)
buchiHypervisor.new_edge(0,1, transitionLabel)
buchiHypervisor.new_edge(1,1, label)
buchiHypervisor.new_edge(1,1, notLabel)
buchiHypervisor.new_edge(1,0, t)



print(buchiHypervisor.to_str('hoa'))

buchiHypervisor.save('buchiHypervisor.hoa')
buchiHypervisor.save('buchiHypervisor.dot','dot')

ret_code = subprocess.call(['dot', '-Tpdf', 'buchiHypervisor.dot', '-o', 'buchiHypervisor.pdf'])
if ret_code == 0:
    print('Human readable Buchi automaton saved at buchiHypervisor.pdf')




#Can we just use a single transition to change from the idle state to the faulty state?
#Can't we have several places that could transition into an area where we would want to be faulty?
