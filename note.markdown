```

f g h
(f g) h

o m a

o o
o m 'T
o.m(a)

m o a




X := {a b c}
Y := {1 2 3}

H := 1 element X
K := 2 element X

p := a  # {a}

H ∊ {{a} {b} {c}}
H_'T | 'T ∊ {a b c}
K ∊ {{a b} {a c} {b c}}
K = (1- element X)


{1 2} ⊆ {1 2 3}


X : {a b c}
Y : {1 2 3}
Z :- X ∪ Y

H_'T | 'T ∊ X

H :  X                    # H = X
H :- X                    # 'T = X | H_'T
H :- {'T  | 'T ∊ X}       # 
H := 'T   | 'T ∊ X        # 
H := {'T} | 'T ∊ X        #

J_'T := {'T} | 'T ∊ Y        # enum


H_'T := {'T} | 'T ∊ X        # enum
H := {'T} | 'T ∊ X           # enum



P := {'T 'E} | ('T ∊ X) ('E ∊ Y)
P :  {'T 'E} | ('T ∊ X) ('E ∊ Y)

P := {'T 'E} | {'T | X} {'E | Y}
P :  {'T 'E} | {'T | X} {'E | Y}

G := 'T | 'T ∊ /_cartesian_{H J}

G := 'T | 'T ∊ {{H_a J_1} {H_a J_2} {H_a J_3} {H_b J_1} {H_b J_2} {H_b J_3} {H_c J_1} {H_c J_2} {H_c J_3}}


Z_'T | 'T ∊ (2 element {X Y G})   # X or Y

XX_'T | 'T ∊ X
YY_'T | 'T ∊ Y

Z_'T  | 'T ∊ {{XX YY} {XX G} {YY G}}



G := 1.element each {}


X : [0x00..0x80]:bit-ranges

comp-pos : <0b0*1..0b0*>

twos-comp ← (
  comp-pos #∪ twos-comp-zero #∪ twos-comp-neg
  | zero : <0b0*>
  | neg  : <0b10*..0b1*>
)

ones-comp ← (
  comp-pos #∪ zero #∪ neg
  | zero : <0b0* 0b1*>
  | neg  : <0b10*..0b1*0>
)

1111



