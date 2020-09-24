import spot
import spot.ltsmin
import subprocess
import os
import sys
import argparse
import buddy
import re

#************************************************#
#  Description HypervisorSlack:
#    Initially uses the MakeBuchi code for
#    converting the promela model into both a
#    kripke structure and a buchi automaton.
#    This code will then take the same ltl 
#    information and use it to generate a
#    hypervisor. If no LTL is specified then no
#    hypervisor will be created, as no transitions
#    can be perturbed.
#************************************************#

#*****************************************************************************************************#
# FUNCTION: extractLabels()
#   This function generates an initial kripke from the model in order to see what labels the model has.
#   It then sorts through those labels and produces a list of labels which is returned. 
#*****************************************************************************************************#
def extractLabels():
    separated_file = []

    #load the model and put it into a kripke structure
    model = spot.ltsmin.load(filename)
    
    print("Making initial kripke to generate labels")
    kripke = model.kripke([])

    print("Done making kripke \n")

    # Save the kripke structure
    kripke.save(model_name + '_kripke.hoa')
    
    #take everything out of the kripke file and put it into a list
    with open(model_name + '_kripke.hoa', "r") as kripkeFile:
        kripkeList = [word for line in kripkeFile for word in line.split()]

    #remove the duplicates from the list
    noDuplicatesList = list(dict.fromkeys(kripkeList))
    
    #remove anything that isn't a label from the list
    findLabelsRegex = re.compile('.*=\d"*')
    labelList = [word for word in noDuplicatesList if findLabelsRegex.search(word)]
    
    #format the labels so that the spot tool can work with them,
    #removing random extra characters and adding ' == ' instead of just '='
    finalList = []
    for word in labelList: 
        newWord = word.replace('"', '')
        newWord = newWord.replace(',', '')
        newWord = newWord.replace('=', ' == ')
        finalList.append(newWord)
    return finalList

#*****************************************************************************************************#
# FUNCTION: userSelectLabel(labelList)
#   This function takes the labels produced from the label list produced by the extractLabels()
#   function. These labels are shown to the user so that they can select which labels they want to 
#   perturb. They select first the label they want to perturb, and then they select which labels 
#   they want to see on the model as well. 
#*****************************************************************************************************#
def userSelectLabel(labelList):
    #First the user will have the option to select the label to be perturbed.
    print("Select the label to be perturbed by entering the number and pressing 'enter'")
    count = 1
    for word in labelList:
        print('{}{}'.format(count, ":"), word + "\n")
        count += 1
    notValid = True
    
    #Here the user inputs their selection, invalid entries are not taken.
    while(notValid):
        index = input("\nYour selection: ")
        try:
            labelIndex = int(index)
            notValid = False
            if((labelIndex > count - 1) | (labelIndex < 1)):
                print("That is not a selection option, please try again")
                notValid = True
        except ValueError:
            print("Only enter the integer value of your selection please")
    labelIndex -= 1
    perturbLabel = labelList[labelIndex]
    print("The label that will be perturbed is: " + perturbLabel + "\n")
    labelList.remove(perturbLabel)      #here the perturbed label is removed from the list
    
    #Second the user will have the option to select a label to observe in addition to the perturbLabel
    print("Select the label to be observed by entering the number and pressing 'enter'")
    count = 1
    for word in labelList:
        print('{}{}'.format(count, ":"), word + "\n")
        count += 1
    notValid = True
    
    #Here the user inputs their selection, invalid entries are not taken.
    while(notValid):
        index = input("\nYour selection: ")
        try:
            labelIndex = int(index)
            notValid = False
            if((labelIndex > count - 1) | (labelIndex < 1)):
                print("That is not a selection option, please try again")
                notValid = True
        except ValueError:
            print("Only enter the integer value of your selection please")
    labelIndex -= 1
    observeLabel = labelList[labelIndex]
    print("The label that will be observed is: " + observeLabel + "\n")
    labelList.remove(observeLabel)
    finalList = [perturbLabel, observeLabel]    #the chosen labels are placed in a list
    return finalList                            #the list is returned for use by the program.


#*****************************************************************************************************#
# FUNCTION: makeBuchi(ltl)
#   This function comes From Bryce Halling's MakeBuchi.py file, it turns a promela model into a buchi
#   object. It needs to have at least 1 ltl specified, but more can be given.  
#*****************************************************************************************************#
def makeBuchi(atomic_propositions):
    print("--------Generating Buchi Automaton with specified ltl--------")

    #***********************************************************#
    # spot takes care of the automaton conversion beginning here.
    #***********************************************************#
    spot.ltsmin.require('spins')
    spot.setup() 

    # Compile the promela file
    model = spot.ltsmin.load(filename)

    # The argument taken here is the atomic proposition(s) to observe in a python list
    print("Making kripke with atomic propositions:")
    print(atomic_propositions)
    k = model.kripke(atomic_propositions)

    print("Done making kripke")

    # Save the kripke structure
    k.save(model_name + '_kripke.hoa')
    k.save(model_name + '_kripke.dot','dot')

    print("Begining buchi conversion. This may take some time")
    buchi = spot.automaton(model_name + '_kripke.hoa').postprocess('BA', 'low', 'small')
    dead = spot.remove_ap()
    dead.add_ap("dead")
    buchi = dead.strip(buchi)
    print("Finished buchi conversion")

    buchi.save(model_name + '_buchi.hoa')
    buchi.save(model_name + '_buchi.dot','dot')

    ret_code = subprocess.call(['dot', '-Tpdf', model_name + '_buchi.dot', '-o', model_name + '_buchi.pdf'])
    if ret_code == 0:
        print('Human readable Buchi automaton saved at ' + model_name + '_buchi.pdf')

    ret_code = subprocess.call(['dot', '-Tpdf', model_name + '_kripke.dot', '-o', model_name + '_kripke.pdf'])
    if ret_code == 0:
        print('Human readable Kripke structure saved at ' + model_name + '_kripke.pdf')
    return buchi, atomic_propositions
    

#*****************************************************************************************************#
#  End of MakeBuchi, this is where the hypervisor generation begins. 
#   A reference for creating automaton via spot can be found at:
#   https://spot.lrde.epita.fr/tut22.html
#*****************************************************************************************************#

def makeHypervisor(buchi, atomic_propositions):
    print("")
    print("--------Generating Hypervisor with specified ltl--------")

    # Creates the dictionary which maintains the correspondance between the
    # atomic propositions and the Boolean decision diagram (bdd) variables that 
    # label the edges of the automaton.
    bdict = spot.make_bdd_dict();

    #makes an empty automaton 
    buchiHypervisor = spot.make_twa_graph(buchi.get_dict()); 

    #turns the atomic propositions into strings, so they can be used as a label
    str_atomic_propositions = "".join([str(elem) for elem in atomic_propositions[0]])
    print(str_atomic_propositions)
    print("")

    #Makes the label based on the atomic propositions
    label = buddy.bdd_ithvar(buchiHypervisor.register_ap(str_atomic_propositions))

    #*********************************************************#
    #This is where the automaton creation begins
    #*********************************************************#
    #This sets the acceptance condition to  Inf(0)&Inf(1)
    buchiHypervisor.set_generalized_buchi(2)

    #Here we decide how many states the automaton will have
    buchiHypervisor.new_states(2)

    #This is where we set the initial state, by default it's 0,
    #but it's still good to set it any ways.
    buchiHypervisor.set_init_state(0)

    #************************************************************#
    #Here is where we define all of the edges of the automaton
    #The first parameter is the initial state, the second is the
    #next state, the third is the label that should be placed
    #there. 
    #The buddy.bddtrue label is how to place a true value.
    #The label is the label we created earlier based on the 
    #atomic propositions
    #************************************************************#
    buchiHypervisor.new_edge(0,0, buddy.bddtrue)
    buchiHypervisor.new_edge(0,1, label)
    buchiHypervisor.new_edge(1,1, label)
    buchiHypervisor.new_edge(1,0, -label)
    buchiHypervisor.new_edge(1,0, -label)

    #Congratulations! The Hypervisor is now created!
    #This prints the .hoa file of the hypervisor to the screen
    #print(buchiHypervisor.to_str('hoa'))

    #Saving the hypervisor to a .hoa and .dot files
    buchiHypervisor.save(model_name + '_Hypervisor.hoa')
    buchiHypervisor.save(model_name + '_Hypervisor.dot','dot')

    #this is to print out the hypervisor to a pdf so that it is easily read.
    ret_code = subprocess.call(['dot', '-Tpdf', model_name + '_Hypervisor.dot', '-o', model_name + '_Hypervisor.pdf'])
    if ret_code == 0:
        print('Human readable Hypervisor automaton saved at ' + model_name + '_Hypervisor.pdf')
    return buchiHypervisor, buchi
     
#*****************************************************************************************************#
# This is where the product of the Hypervisor and the Model begins.
#*****************************************************************************************************#
def product(buchiHypervisor, buchi):
    product = spot.product(buchiHypervisor, buchi)

    product.save(model_name + '_Product.hoa', 'hoa')
    product.save(model_name + '_Product.dot','dot')
    ret_code = subprocess.call(['dot', '-Tpdf', model_name + '_Product.dot', '-o', model_name + '_Product.pdf'])
    if ret_code == 0:
        print('Human readable Product automaton saved at ' + model_name + '_Product.pdf')
    for s in range(0, product.num_states()):
        print("State{}:".format(s))
        for t in product.out(s):
            print("edge({} -> {})".format(t.src,t.dst))
            print("     label = ", spot.bdd_format_formula(product.get_dict(), t.cond))

#*****************************************************************************************************#
#  FUNCTION: main
#    This is the start of the program. Initially arguments are parsed then functions are called:
#      makeBuchi - turns the promela model provided into a buchi automaton object
#      makeHypervisor - this takes the ltl provided to generate a hypervisor
#      product - this performs the product of the model and hypervisor and save the result.
#*****************************************************************************************************#
if __name__ == "__main__":
    #This is where the argument parsing begins
    parser = argparse.ArgumentParser(description='turn a promela specification into a buchi automaton')
    parser.add_argument('filename', 
            metavar='<filename>', 
            type=str, 
            nargs=1, 
            help='The promela specification to be used')
    parser.add_argument('-c', '--clean', 
            action='store_true', 
            help='Clean the files made by previous runs. Requires specification of the model used in the previous run.')

    args = parser.parse_args()

    filename = args.filename[0]
    model_name = filename[0:-4]

    if args.clean:
        no_path_filename = filename.split('/')[-1]
        ret_code = subprocess.call(['rm', model_name + '_kripke.hoa', model_name + '_kripke.dot', model_name + '_kripke.pdf', model_name + '_buchi.hoa', model_name + '_buchi.dot', model_name + '_buchi.pdf', no_path_filename + '.spins', no_path_filename + '.spins.c', model_name + '_Hypervisor.dot', model_name + '_Hypervisor.pdf', model_name + '_Hypervisor.hoa', model_name + '_Product.dot', model_name + '_Product.hoa', model_name + '_Product.pdf'])
        if ret_code != 0:
            sys.exit(1)
        sys.exit(0)

    labelList = extractLabels()
    finalList = userSelectLabel(labelList)
    buchi, atomic_propositions = makeBuchi(finalList)
    buchiHypervisor, buchi = makeHypervisor(buchi, atomic_propositions)
    product(buchiHypervisor, buchi)
