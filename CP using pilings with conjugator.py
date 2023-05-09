# -*- coding: utf-8 -*-
"""
Created on Tue Jan 10 13:47:24 2023

@author: Gemma Crowe, Michael Jones
"""

# -*- coding: utf-8 -*-

import copy
from PIL import Image, ImageDraw, ImageFont
from math import sin, cos, pi
import networkx as nx

#Program: Conjugacy problem in RAAGs
#Method: Crisp, Godelle, Wiest linear-time algorithm
#Algorithm returns TRUE/FALSE
#as well as conjugator element


def piling(w, N, commuting_elements=[]):
    #INPUT: w = word, N = size of generating set
    #commuting_elements = list of tuples representing
    #edges in defining graph
    #OUTPUT: piling represented as list of lists
    #one for each column of the piling
    
    #First, we find the number of columns needed.
    #This is precisely the number of generators of the RAAG.
    columns = N
    piling = []
    for i in range(0, columns):
        piling.append([]) #This makes all the empty columns
    for l in w: 
        #For each letter in the word
        #We perform this quick check to see if the column has anything in it
        #If not we don't need to bother checking if we need to cancel
        if len(piling[abs(l)-1]) > 0:
            #Here we check if we are putting a '+' bead on top of a '-' bead
            if piling[abs(l)-1][len(piling[abs(l)-1])-1] == -1 and l > 0:
                #Instead of combining, we cancel
                #Also need to remove corresponding 0 tiles
                for i in range(0, len(piling)):                  
                    if not(((i+1,l) in commuting_elements) or ((l,i+1) in commuting_elements)):
                        piling[i].pop(len(piling[i])-1)
                        #Note: this includes - tile since (l,l) is not in 
                        #commuting_elements
            #Here we check if we are putting a '-' bead on top of a '+' bead
            elif piling[abs(l)-1][len(piling[abs(l)-1])-1] == 1 and l < 0:
                for i in range(0, len(piling)):
                    if not(((i+1,-l) in commuting_elements) or ((-l,i+1) in commuting_elements)):
                        piling[i].pop(len(piling[i])-1)
            else:
                #If there is no cancellation we just pile it on top
                for i in range(0, len(piling)):
                    if i+1 == abs(l):
                        if l > 0:
                            piling[i].append(1)
                        else:
                            piling[i].append(-1)
                    else:
                        if not(((i+1,abs(l)) in commuting_elements) or ((abs(l),i+1) in commuting_elements)):
                            piling[i].append(0)
        else:
            #If there is no cancellation we just pile it on top
            for i in range(0, len(piling)):
                if i+1 == abs(l):
                    if l > 0:
                        piling[i].append(1)
                    else:
                        piling[i].append(-1)
                else:
                    if not(((i+1,abs(l)) in commuting_elements) or ((abs(l),i+1) in commuting_elements)):
                        piling[i].append(0)
    return(piling)

def normal_form_rep(p, commuting_elements=[]):
    #INPUT: p = piling, commuting_elements
    #OUTPUT: normal reduced representative of p as a word
    #Note: we order opposite to CGW paper, i.e. Shortlex
    #i.e. 1, -1 < 2, -2 < 3, -3 < ...
    
    #Create empty word
    word = []
    #Copy piling
    piling = copy.deepcopy(p)
    while piling != [[]] * len(piling): 
        #While piling not empty
        #These next lines find the leftmost column that a
        #letter can be taken from
        l = 1
        while True:
            if piling[l-1] != []:
                if piling[l-1][0] != 0:
                    break
                else:
                    l += 1
            else:
                l += 1
        #Now we add the letter to the word
        word.append(l * piling[l-1][0])
        #Finally we remove the relevant balls from the piling
        for i in range(0, len(piling)):
            if l == i+1:
                piling[i].pop(0)
            elif not(((i+1,abs(l)) in commuting_elements) or ((abs(l),i+1) in commuting_elements)):
                piling[i].pop(0)
    return(word)

def cyclically_reduce(p, commuting_elements=[]):
    #INPUT: p = piling, commuting_elements
    #OUTPUT: cyclically reduced piling, and conjugator (word)
    Conj = []
    #First rule out empty piling
    w = normal_form_rep(p, commuting_elements)
    if w ==[]:
        return p
    #Copy piling
    piling = copy.deepcopy(p)
    #Initially assume it's not cyclically reduced
    cyclically_reduced = False
    while not cyclically_reduced:
        #Initially assume it's cyclically reduced until we find a column that isn't
        cyclically_reduced = True
        for i in range(0, len(piling)):
            if piling[i] != []:
                if piling[i][0] != 0 and piling[i][0] == -piling[i][len(piling[i])-1]:
                    cyclically_reduced = False
                    #Add to conjugator - as a letter in a word
                    sign = piling[i][0]
                    if sign == 1:
                        Conj.append(i+1)
                    else:
                        Conj.append(-(i+1))
                    #Remove the necessary balls
                    for j in range(0, len(piling)):
                        if not((j+1, i+1) in commuting_elements or (i+1, j+1) in commuting_elements) or j == i:
                            piling[j].pop(len(piling[j])-1)
                            piling[j].pop(0)
    return(piling, Conj)

#The next set of functions allow us to input
#our defining graph.
#We then use networkx to look at connected components
#for the factorising step of the algorithm
#Note: CGW convention: edges for non-commuting elements

def graph_from_edges(N, commuting_edges=[]):
    #INPUT: list of edges, N=size of generating set
    #i.e. N = number of vertices in defining graph
    #OUTPUT: networkx graph with edges for non-commuting
    G = nx.Graph()
    G.add_nodes_from(range(1,N+1))
    G.add_edges_from(commuting_edges)
    #Need to take compliment to have edges for non-commuting
    g = nx.complement(G)
    return g

def supp_piling(p):
    #INPUT: piling
    #OUTPUT: support of word which represents piling, as a list
    l = []
    n = len(p)
    for i in range(0, n):
        column = p[i]
        if column !=[]:
            #If column non-empty, check if it contains +-1 tile
            m = len(column)
            for j in range(0,m):
                if abs(column[j]) == 1:
                    l.append(i+1)
                    break
    return l


def factorise(g, p):
    #INPUT: g = defining graph of RAAG, p = piling
    #OUTPUT: list of subgraphs for each connected component of g
    supp = supp_piling(p)
    #Compute subgraph of g based on support of word
    sub = g.subgraph(supp)
    s = [sub.subgraph(c) for c in nx.connected_components(sub)]
    return s

def graph_to_nsfactor(g, w):
    #INPUT: g = connected component of defining graph, w = word
    #OUTPUT: non-split factor based on word
    #For each connected component, find non-split factor
    #of word w
    l = []
    vert = list(g.nodes())
    for x in w:
        if abs(x) in vert:
            l.append(x)
    return l

def graphs_to_nsfactors(l, w, N, commuting_elements):
    #INPUT: l = list of subgraphs (all connected components), w=word
    #OUTPUT: list of nsfactors of w as pilings
    m = []
    for x in l:
        #For each subgraph, find non-split factor as a 
        #subword of w
        fact = graph_to_nsfactor(x, w)
        #Convert word to piling
        pile = piling(fact, N, commuting_elements)
        m.append(pile)
    return(m)
        
#This function takes a non-split, cyclically
#reduced piling and returns p0 and p1
def pyramidal_decomp(p, commuting_elements=[]):
    #INPUT: p = piling, conjugator element (from cyclic reduction)
    #Assume p is non-split, cyclically reduced
    #OUTPUT: factors p0, p1 of p, as pilings
    
    #If the piling is empty we must do this or else the
    #program will get stuck in an infinite loop trying
    #to find the apex
    if normal_form_rep(p, commuting_elements) == []:
        return((copy.deepcopy(p), copy.deepcopy(p)))
    #initial p0 and p1
    p1 = copy.deepcopy(p)
    p0 = [[] for i in p1]

    #Firstly we need to find the apex column
    #We rule out columns which contains only
    #0 tiles
    apex = 1
    while p1[apex-1] == [0] * len(p1[apex-1]):
        apex += 1

    #Now we need to iteratively reduce p1
    done = False
    while not done:
        done = True
        for i in range(apex, len(p1)): #apex-1+1 = apex
            #We need to make sure it's not empty
            if p1[i] != []:
                #if it begins with 1 or -1
                if abs(p1[i][0]) == 1:
                    #move tile to p0
                    for j in range(0, len(p1)):
                        if not(((i+1, j+1) in commuting_elements) or ((j+1, i+1) in commuting_elements)):
                            p0[j].append(p1[j].pop(0))
                    done = False
                    break

    return(p0, p1)


def product(p1, p2, N, commuting_elements=[]):
    #This function quite simply returns the product
    #of two given pilings
    return(piling(normal_form_rep(p1, commuting_elements) + normal_form_rep(p2, commuting_elements), N, commuting_elements))

def pyramidal(p, N, commuting_elements=[]):
    #INPUT: P = non-split, cyclically reduced piling, conjugator
    #OUTPUT: pyramidal piling of P
    #using sequence of cycles
    piling = copy.deepcopy(p)
    #I use an infinite loop with a conditional
    #statement containing the exit condition so
    #I can check the condition at the END of
    #each iteration, not the start
    Conj = []
    while True:
        p0, p1 = pyramidal_decomp(piling, commuting_elements)
        if normal_form_rep(p0, commuting_elements) == []:
            return(p1, Conj)
        else:
            #Add p0 factor to conjugator
            conj = normal_form_rep(p0, commuting_elements)
            for x in conj:
                Conj.append(x)
            piling = product(p1, p0, N, commuting_elements)


def cyclic_permutation(w, n):
    #This function calculates the nth cyclic permutation of w
    v = [w[i%len(w)] for i in range(n, len(w)+n)]
    #This might not be the most readable way to do it but it's quicker than the naive way
    return(v)

def is_cyclic_permutation(w, v): 
    #This function decides if two words are cyclic permutations of each other
    Conj = []
    if len(w) == len(v):
        cp = False
        for i in range(0, len(w)):
            if cyclic_permutation(w, i) == v:
                #Once found, add to conjugator
                for x in range(0,i):
                    Conj.append(w[x])               
                cp = True
                #Once we find a correct i, we don't need to check the rest
                break
        return(cp, Conj)
    else:
        return(False)
    
def inverse_word(w):
    #To compute conjugator, need to take inverse of a word
    #INPUT: word w
    #OUTPUT: word representing w^-1
    rev = w[::-1]
    new = []
    for x in range(0, len(rev)):
        new.append(-rev[x])
    return new

def is_conjugate(w1, w2, N, commuting_elements=[]):
    #INPUT: w1, w2 = words, N = number of vertices 
    #in induced graph
    #OUTPUT: True or False if w1 is conjugate to w2
    
    #Keep track of conjugator element as we go
    Conj_p, Conj_q = [], []
    #Step (i): produce cyclically reduced
    #pilings p and q
    pile_p, pile_q = piling(w1, N, commuting_elements), piling(w2, N, commuting_elements)
    #Trivial check: if two reduced elements in normal form are equal in the RAAG, then conjugate
    if pile_p == pile_q:
        return (True, [])    
    p_cyc, q_cyc = cyclically_reduce(pile_p, commuting_elements), cyclically_reduce(pile_q, commuting_elements)
    #Extract pilings and conjugator elements
    Conj_p = Conj_p + p_cyc[1]
    Conj_q = Conj_q + q_cyc[1]
    p, q = p_cyc[0], q_cyc[0]
    #Step (ii): factorise p and q into non-split factors.
    graph = graph_from_edges(N, commuting_elements)
    p_nsf, q_nsf = factorise(graph, p), factorise(graph, q) 
    #To check whether the collection of subgraphs
    #coincide is equivalent to checking whether the
    #subgraphs in each set coincide.
    #This can be done easily using set equality
    word_p, word_q = normal_form_rep(p, commuting_elements), normal_form_rep(q, commuting_elements)
    factors_p, factors_q = graphs_to_nsfactors(p_nsf, word_p, N, commuting_elements), graphs_to_nsfactors(q_nsf, word_q, N, commuting_elements)
    if set([frozenset([abs(j) for j in normal_form_rep(i, commuting_elements)]) for i in factors_p]) != set([frozenset([abs(j) for j in normal_form_rep(i, commuting_elements)]) for i in factors_q]):
        return(False)
    #We now need to match up nsf's from
    #p and q to test them against each other
    #First convert subgraphs to non-split factors
    #We fix the order of p_nsf, and change the order of q_nsf to match
    factors_q_new = [] #new list
    for i in range(0, len(factors_p)):
        for j in range(0, len(factors_q)):
            if set([abs(j) for j in normal_form_rep(factors_p[i], commuting_elements)]) == set([abs(j) for j in normal_form_rep(factors_q[j], commuting_elements)]):
                factors_q_new.append(factors_q.pop(j))
                break
    #Now they are matched, it remains to check each nsf
    #First find pyramidal pilings
    #Then check if equal up to cyclic normal form
    #i.e. equals up to cyclic permutation
    for i in range(0, len(factors_p)):
        pyr_pi, pyr_qi = pyramidal(factors_p[i], N, commuting_elements), pyramidal(factors_q_new[i], N, commuting_elements)
        #Extract pyramid and conjugator element
        Conj_p = Conj_p + pyr_pi[1]
        Conj_q = Conj_q + pyr_qi[1]
        pyr_pi_pile, pyr_qi_pile = pyr_pi[0], pyr_qi[0]
        if not is_cyclic_permutation(normal_form_rep(pyr_pi_pile, commuting_elements), normal_form_rep(pyr_qi_pile, commuting_elements))[0]:
            return False
        else:
            #If true, add to conjugator
            cycle = is_cyclic_permutation(normal_form_rep(pyr_pi_pile, commuting_elements), normal_form_rep(pyr_qi_pile, commuting_elements))
            Conj_p = Conj_p + cycle[1]
    #If the algorithm gets this far, the answer is YES
    #Also want to return conjugator element
    rev_q = inverse_word(Conj_q)
    Conj_full = Conj_p + rev_q
    pile = piling(Conj_full, N, commuting_elements)
    conjugator = normal_form_rep(pile, commuting_elements)
    return(True, conjugator)

#Aside: visual interpretation of pilings
def draw_piling(piling, scale=100.0, plus_colour=(255,50,0), zero_colour=(150, 150, 150), minus_colour=(50,100,250), anti_aliasing=4, filename="piling.png", show=True, save=True):
    #This function creates an image file containing a visual
    #representation of the given piling with several
    #customisable parameters. To render nice smooth anti-
    #aliased pilings, by default the function uses supersampling.
    #For better performance use anti_aliasing=1.
    columns = len(piling)
    rows = max([len(i) for i in piling])
    aa_scale = scale * anti_aliasing
    image_width = int(aa_scale * (columns + 1))
    image_height = int(aa_scale * (rows + 1))
    
    image = Image.new(mode="RGB", size=(image_width, image_height), color=(255, 255, 255))
    draw = ImageDraw.Draw(image)

    draw.line(((aa_scale/2.0, image_height-(aa_scale/2.0)), (image_width-(aa_scale/2.0)), image_height-(aa_scale/2.0)), fill=(0, 0, 0), width=int(aa_scale/25.0))
    for i in range(0, len(piling)):
        for j in range(0, len(piling[i])):
            if piling[i][j] == 1:
                draw.ellipse((int(aa_scale * (0.5 + i)), int(image_height - (aa_scale * (1.5 + j))), int(aa_scale * (1.5 + i)), int(image_height - (aa_scale * (0.5 + j)))), outline=plus_colour, width=int(aa_scale/25.0))
                draw.line(((int(aa_scale * (0.75 + i)), int(image_height - (aa_scale * (j + 1)))), (int(aa_scale * (1.25 + i)), int(image_height - (aa_scale * (j + 1))))), fill=plus_colour, width=int(aa_scale/25.0))
                draw.line(((int(aa_scale * (1 + i)), int(image_height - (aa_scale * (j + 0.75)))), (int(aa_scale * (1 + i)), int(image_height - (aa_scale * (j + 1.25))))), fill=plus_colour, width=int(aa_scale/25.0))
            elif piling[i][j] == -1:
                draw.ellipse((int(aa_scale * (0.5 + i)), int(image_height - (aa_scale * (1.5 + j))), int(aa_scale * (1.5 + i)), int(image_height - (aa_scale * (0.5 + j)))), outline=minus_colour, width=int(aa_scale/25.0))
                draw.line(((int(aa_scale * (0.75 + i)), int(image_height - (aa_scale * (j + 1)))), (int(aa_scale * (1.25 + i)), int(image_height - (aa_scale * (j + 1))))), fill=minus_colour, width=int(aa_scale/25.0))
            else:
                draw.ellipse((int(aa_scale * (0.5 + i)), int(image_height - (aa_scale * (1.5 + j))), int(aa_scale * (1.5 + i)), int(image_height - (aa_scale * (0.5 + j)))), outline=zero_colour, width=int(aa_scale/25.0))

    image = image.resize((image_width // anti_aliasing, image_height // anti_aliasing), resample=Image.ANTIALIAS)
    if save:
        image.save(filename)
    if show:
        image.show()
    
#Examples and testing
from nose.tools import ok_

#1: Free groups
x1 = [1,2,-1,3,-4,2]
x2 = [3,-4,2,1,2,-1]
ok_(is_conjugate(x1,x2,4) == (True, [-2,4,-3]))
#x3: non-CR word conjugate to x2
x3 = [2, 3,-4,2,1,2,-1, -2]
ok_(is_conjugate(x1,x3,4) == (True, [-2,4,-3,-2]))
x4 = [1,2,1,3,-4,2]
#x4 not conjugate to any of x1, x2, x3
ok_(is_conjugate(x1, x4, 4) == is_conjugate(x2, x4, 4) == is_conjugate(x3, x4, 4) == False)
#Test conjugacy to empty words
empty = []
x5 = [2,-2,-4,4]
ok_(is_conjugate(empty, x5, 4) == (True, []))

#2: Free abelian
a1 = [1,2,-1,3,-4,2]
a2 = [2,-4,2,3]
edge_free_abelian = [(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]
ok_(is_conjugate(a1, a2, 4, edge_free_abelian))
#a1, a2 conjugate in Z^4
a3 = [1,2,-1,3,4,-2,-4,-3]
ok_(is_conjugate(empty, a3, 4, edge_free_abelian)== (True, []))

#3: RAAG defined in Crisp-Godelle-Wiest paper
CGW_Edges = [(1,4), (2,3), (2,4)]

#Example of non-CR, non-reduced word
nonCR_nonRw = [-2,-2,-4,3,2,4,1,2,-1,2,2,-4]
p1 = piling(nonCR_nonRw, 4, CGW_Edges)
#Example where 2 cyclic reductions need to be made
nonCR2_nonRw = [3, -2,-2,-4,3,2,4,1,2,-1,2,2,-4, -3]
p2 = piling(nonCR2_nonRw, 4, CGW_Edges)

#Test cyclic reduction
cycp1 = cyclically_reduce(p1, CGW_Edges)
cycp2 = cyclically_reduce(p2, CGW_Edges)
ok_(cycp1[0] == cycp2[0])
#These two pilings cyclically reduce to the same piling

#Test factorisation
p3 = piling([-2,3,1,2,-1,2], 4, CGW_Edges)
g = graph_from_edges(4, CGW_Edges)
f1 = factorise(g, p3)
#Example: split word
#See Figure 4 of CGW paper
p4 = piling([2,3,-4], 4, CGW_Edges)
f2 = factorise(g, p4)
f2_facts = graphs_to_nsfactors(f2, [2,3,-4], 4, CGW_Edges)
word_f2_facts = (normal_form_rep(f2_facts[0], CGW_Edges), normal_form_rep(f2_facts[1], CGW_Edges))
ok_(word_f2_facts == ([2], [3,-4]))
#Word factorises into a_{2} and a_{3}a^{-1}_{4}

#Pyramidal decomposition
pyr1 = pyramidal_decomp(cycp1[0], CGW_Edges)
pyr11 = pyramidal(cycp1[0], 4, CGW_Edges)


#Test conjugacy function
t1 = [-2,-2,-4,3,2,4,1,2,-1,2,2,-4]
t2 = [4,3,-4,2,1,2,-1,-4]
ok_(is_conjugate(t1, t2, 4, CGW_Edges) == (True, [-2,-2,-4,-4]))
#t1 is conjugate to t2 in CGW RAAG
t3 = [4,3,-1,2,1,2,-1,-4]
ok_(is_conjugate(t1, t3, 4, CGW_Edges) == is_conjugate(t2, t3, 4, CGW_Edges))
#t3 is not conjugate to either t1 or t2


#4: Path on 5 points (different number of generators)
edge_path = [(1,2), (2,3), (3,4), (4,5)]
b1 = [3,-2,4,-5,2,1,-3,4]
b2 = [-5,2,1,5,4,-5,-2, 4]
ok_(is_conjugate(b1, b2, 5, edge_path) == (True, [-2,3,4]))
#b1,b2 are conjugate

