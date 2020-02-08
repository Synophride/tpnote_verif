/* -------------------------------------------------------------------------- */
/*
  Ce fichier implémente une structure de données, appelée qstack, permettant
  d'accéder rapidement au dernier élément ajouté (comme une pile LIFO), mais
  permettant d'ajouter aussi facilement un élément à la fin (comme une file
  FIFO). Pour cela, sa représentation interne est composée d'une pile et d'une
  file, représentées ici par des tableaux.
  
  Votre but est de:

  1. prouver l'absence d'erreurs à l'exécution de toutes les fonctions
  (en ajoutant les préconditions ACSL nécessaires) ; il est conseillé  
  commencer par cette question.

  2. donner une spécification informelle (en français ou en anglais) pour chacun
  des prédicats de l'axiomatique [Transfer].

  3. écrire et prouver la spécification ACSL des fonctions fournies, à partir 
  des spécifications informelles indiquées, et en respectant les consignes.
*/
/* -------------------------------------------------------------------------- */

/* -------------------------------------------------------------------------- */
/* Définition de la structure de données
/* -------------------------------------------------------------------------- */

/* [MAX_SIZE] est la taille maximale des piles et des files. */
#define MAX_SIZE 8

/* [elt] est le type des éléments composants une qstack. */
typedef unsigned char elt;

/* [xifo] est le type des piles et des files. */
typedef struct {
  elt content[MAX_SIZE]; // contenu d'une bxifo
  int size;              // nombre d'éléments
} xifo;

/* [qstack] est le type des qstacks. */
typedef struct {
  xifo stack; // pile interne:
              // son sommet (le début) est à l'index [stack.size];
              // le bas (la fin) de la pile est à l'index 0.
  xifo queue; // file interne
              // la tête de la file est à l'index 0;
              // la queue de la file est à l'index [queue.size].
  // les plus anciens éléments sont donc toujours dans les bas indices
  // (en bas de pile ou en tête de file); et
  // les plus récents sont dans les indices plus élevés
  // (en sommet de pile ou en queue de file)
} qstack;

/* -------------------------------------------------------------------------- */
/* [clear(qs)] vide une qstack. */
/* -------------------------------------------------------------------------- */

/*@requires \valid(qs);
  @assigns qs->stack.size, qs->queue.size;
@ */ 
void clear(qstack *qs) {
  qs->stack.size = 0;
  qs->queue.size = 0;
}

/* -------------------------------------------------------------------------- */
/* Voici quelques prédicats qui pourront être utiles par la suite...
   Donnez une spécification informelle de chacune d'eux, en français ou en
   anglais.

   Vous noterez la syntaxe "predicate p{L1,L2}(...) = ..." qui est une extension
   de la syntaxe vue en cours et qui permet de faire dépendre la définition du
   prédicat [p] des points de programme [L1] et [L2].

   Au point d'appel, il faut expliciter [L1] et [L2], par exemple de la façon 
   suivante: "assert p{Pre,Here}(...);"
*/
/* -------------------------------------------------------------------------- */


/*@ axiomatic Transfer {
  @   predicate stackHasShifted{L1,L2}(xifo *stack, integer offset) =
  @     \forall integer i; 0 <= i < \at(stack->size, L1) - offset ==>
  @       \at(stack->content[i+offset], L1) == \at(stack->content[i], L2);
  // L1 :
  //   <--   stack->size   -->
  //   [<offset>| c1, c2, c3 ]
  //             <--      --> = (stack->size) - offset
  // L2 :
  //   [c1, c2, c3] 
  
  @   predicate queueHasShifted{L1,L2}(xifo *queue, integer offset) =
  @     \forall integer i; 0 <= i < \at(queue->size, L1) - 1 ==>
  @       \at(queue->content[i], L1) == \at(queue->content[i+offset], L2);
  // décalage
  // L1 :  ( queue -> contents ) [queue->contents[ 0 -> queue->size ]  
  //   ([e1, e2, e3, e4], N, N+1...) 
  // L2 : 
  //   (0, 1, ..., offset-1, [e1, e2, e3, e4], N+offset, ...) 

  @   predicate isTransferred{L1,L2}
  @     (xifo *stack, xifo *queue, integer offset) =
  @     \forall integer i; 0 <= i < offset ==>
  @       \at(stack->content[offset-i-1], L1) == \at(queue->content[i], L2);
  // Le stack stocke les memes éléments que la queue sur l'intervalle [0 : offset[
  // dans le sens inversé. Vérifie le transfert pile -> queue
  //
  // L1 : 
  //  stack : [ e1, e2, e3, e4 ] 
  // L2 :
  //  queue : [ e4, e3, e2, e1 ]
  // Meme ordre si on retire les objets 
  @ } */

// Transfer 
/* -------------------------------------------------------------------------- */
/* [pop(qs)] enlève le sommet de la pile.

   La spécification formelle doit notamment préciser, pour chaque comportement:
   - le résultat retourné
   - la taille des éléments internes de [qs]
   - le contenu des éléments internes de [qs] (par rapport à l'état initial)
 */

/*@
  @ requires \valid(qs);
  @ requires \separated(qs->stack.content, qs->queue.content);
  @ requires \valid(qs->stack.content+(0 .. MAX_SIZE-1));
  @ requires \valid(qs->queue.content+(0 .. MAX_SIZE-1));  
  @ requires 0 <= qs->queue.size <= MAX_SIZE;
  @ requires 0 <= qs->stack.size <= MAX_SIZE;
  
  @ assigns qs->stack.size;
  @ assigns qs->queue.size;
  @ assigns qs->queue.content[0 .. MAX_SIZE-1];

  @ behavior empty:
  @    assumes qs->stack.size == 0 && qs->queue.size==0;
  @    
  @    ensures \result == -1;
  @    assigns \nothing;
  
  @ behavior stack_empty:
  @    assumes qs->stack.size == 0 && qs->queue.size > 0;
  @    
  @    ensures \result == \old(qs->queue.content[0]);
  @    ensures qs->stack.size == 0 ;
  @    ensures qs->queue.size == \old(qs->queue.size) - 1;
  @    ensures \forall integer i; 0 <= i < qs->queue.size
  @        ==> qs->queue.content[i] == \old(qs->queue.content[i+1]);
  @
  @    assigns qs->queue;
  @    assigns qs->queue.size;
  @    assigns qs->queue.content[ 0 .. MAX_SIZE-1];
  
  @ behavior filled:
  @   assumes qs->stack.size > 0 && qs->queue.size >= 0;
  @   
  @   ensures \result == qs->stack.content[qs->stack.size];
  @   ensures qs->stack.size == \old(qs->stack.size) - 1;
  @  
  @   assigns qs -> stack.size;

  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int pop(qstack *qs) {    
    if (qs->stack.size == 0) {

	if (qs->queue.size == 0)
	    return -1;
	
	qs->queue.size--; 
	int res = qs->queue.content[0];
	
	/*@ loop invariant 0 <= i <= qs->queue.size < MAX_SIZE;
	  @ loop invariant \forall integer j; 0 <= j < i
	  @      ==> qs->queue.content[j] 
	  @       == \at(qs->queue.content[j+1], LoopEntry);
	  @ 
	  @ loop invariant \forall integer j; i <= j < MAX_SIZE 
	  @      ==> qs->queue.content[j] 
	  @       == \at(qs->queue.content[j], Pre);

	  @ loop assigns qs->queue.content[0 .. MAX_SIZE - 1], i;
	*/
	for(int i = 0; i < qs->queue.size; i++)
	    qs->queue.content[i] = qs->queue.content[i+1];
	return res;
    }
    
    qs->stack.size--;
    return qs->stack.content[qs->stack.size];
}

/* -------------------------------------------------------------------------- */
/* [transfer(src, dst)] est une fonction auxiliaire de [push] et [enqueue] qui
   transfère les [(MAX_SIZE - dst->size) / 2)] (+ 1 si la différence est
   impaire) plus anciens éléments de [src] à la fin de [dst].
r
   La spécification formelle doit notamment préciser, pour chaque comportement:
   - le résultat retourné
   - la taille des éléments internes de [qs]
   - le contenu des éléments internes de [qs] (par rapport à l'état initial)
*/

/*@ requires \valid(src);
  @ requires \valid(dst);
  @ requires \separated(src, dst); 
  @ requires 0 <= src->size <= MAX_SIZE; 
  @ requires 0 <= dst->size <= MAX_SIZE;

  @ behavior full:
  @   assumes src->size == dst->size == MAX_SIZE; 
  @   ensures \result == 0; 
  @   assigns \nothing;
  
  @ behavior space_left:
  @   assumes src->size < MAX_SIZE;
  @   ensures \result == 1;
  @   assigns \nothing;
  
  @ behavior transfert: 
  @   assumes src->size == MAX_SIZE && dst->size < MAX_SIZE;
  @   
  @   // Décalage des éléments de dst
  @   ensures BAGUETTE: // ce début est cadeau
  @     \let size = MAX_SIZE - \at(dst->size, Pre);
  @     \let offset = size % 2 == 0 ? size / 2 : size / 2 + 1;
  @     \forall integer i; (0 <= i < MAX_SIZE - offset
  @       ==> (src->content[i] == \old(src->content[i + offset])));

  @   ensures CROISSANT: 
  @     \let size = MAX_SIZE - \at(dst->size, Pre);
  @     \let offset = size % 2 == 0 ? size / 2 : size / 2 + 1;
  @     \forall integer i; ( 0 <= i < \old(dst->size) 
  @       ==> dst->content[i + offset] == \old(dst->content[i]));
  
  @   ensures FROMAGE: 
  @     \let size = MAX_SIZE - \at(dst->size, Pre);
  @     \let offset = size % 2 == 0 ? size / 2 : size / 2 + 1;
  @    \forall integer i; 0<=i<offset 
  @       ==> dst->content[i] == \old(src->content[offset - i - 1]);

  
  @   assigns src->size, src->content[ 0 .. MAX_SIZE - 1];
  @   assigns dst->size, dst->content[ 0 .. MAX_SIZE - 1];
  
  
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int transfer(xifo *src, xifo *dst) {
  if (src->size == MAX_SIZE) {
    if (dst->size == MAX_SIZE)
      return 0;
    else {
      int size = MAX_SIZE - dst->size;
      int offset = size % 2 == 0 ? size / 2 : size / 2 + 1;
      int i=0; // Ajout du = 0,
      // plus facile pour la preuve mais pas forcément pour les points 
      
      /*@ loop invariant (-1 <= i < dst->size);
	@ loop invariant \forall integer j; -1 <= i < j < dst->size
	@      ==>     dst->content[ j + offset ]
	@       == \at(dst->content[ j ], LoopEntry);
	
	@ loop invariant \forall integer j; 0 <= j <= i 
	@      ==>  dst->content[ j ]
	@       == \at(dst->content[ j ], LoopEntry);
	
	@ loop assigns dst->content[0 .. MAX_SIZE - 1], i;
	
	@ loop variant i;
	@*/ 
      for(i = dst->size-1; i >= 0; i--)
	  dst->content[i+offset] = dst->content[i];
        
      /*@ loop invariant orange: 0 <= i <= offset < MAX_SIZE; 
	
	@ loop invariant endive: \forall integer j; 0 <= j < i
	@      ==> dst->content[j]
	@       == src->content[offset - 1 - j  ];
	
	@ loop invariant couscous: \forall integer j;  i <= j < MAX_SIZE
	@      ==> dst->content[j] == \at(dst->content[j], LoopEntry);

	@ loop assigns dst->content[ 0 .. MAX_SIZE - 1], i;
	
	@ loop variant offset - i;
	@ */
      for(i = 0; i < offset; i++)
	  //  copie des <offset> derniers éléments de src
	  // vers les <offset> premiers éléments de dst
	  dst->content[i] = src->content[offset-i-1];
      
      /*@ loop invariant borne: 0 <= i <= src->size-offset < MAX_SIZE; 
	
	@ loop invariant betterave: \forall integer j; 0 <= j< i
	@      ==> src->content[j]
	@       == \at( src->content[ j+offset ], LoopEntry );

	@ loop invariant banane:
	@   \forall integer j; i <= j < MAX_SIZE
	@      ==> src->content[j]
	@       == \at(src->content[j], LoopEntry);
	
	@ loop assigns src->content[ 0 .. MAX_SIZE - 1], i;
	
	@ loop variant (src->size - offset) - i;
      */
      for( i = 0; i < src->size-offset; i++ )
	  // décalage des éléments de <offset> vers la gauche
	  src->content[i] = src->content[i+offset];
      //@assert pouet: offset >= 0;
      src->size -= offset;
      dst->size += offset;
      
      /* les assertions suivantes sont nécessaires avec certaines versions de
         Frama-C et Alt-Ergo. Elles doivent être prouvées. */

      /*@assert champignon: \at(src->size, Pre) + \at(dst->size, Pre) == src->size + dst->size;*/
      /*@assert oignon: queueHasShifted{Pre,Here}(dst, offset);*/
      /*@assert echalote: isTransferred{Pre,Here}(src, dst, offset); */
      /*@assert ail: stackHasShifted{Pre,Here}(src, offset); */

    }
    
  }
  return 1;
}

/* -------------------------------------------------------------------------- */
/* [push(qs)] ajoute un élément au sommet de la pile.

   La spécification formelle doit notamment préciser, pour chaque comportement:
   - le résultat retourné
   - le contenu des éléments internes de [qs] (par rapport à l'état initial)
   - la taille des éléments internes de [qs]
*/
/* -------------------------------------------------------------------------- */

/*@ requires \true;   // à compléter
  @
  @ assigns \nothing; // à compléter
  @
  @ behavior full: // [qs] est complet
  @   ensures \true;  // à compléter
  @
  @ behavior space_left: // la pile de [qs] a au moins un espace libre
  @   ensures \true; // à compléter
  @
  @ behavior transfer: // la pile de [qs] est complète, mais pas sa file
  @   ensures \true; // à compléter
  @   ensures // ce début est cadeau:
  @     \let size = MAX_SIZE - \at(qs->queue.size, Pre);
  @     \let offset = size % 2 == 0 ? size / 2 : size / 2 + 1;
  @     \true;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @ */
int push(qstack *qs, elt e) {
  if (! transfer(&qs->stack, &qs->queue))
    return -1;
  qs->stack.content[qs->stack.size] = e;
  qs->stack.size++;
  return e;
}

/* -------------------------------------------------------------------------- */
/* [enqueue(qs)] ajoute un élément au bout de la file.

   La spécification formelle doit notamment préciser, pour chaque comportement:
   - le résultat retourné
   - le contenu des éléments internes de [qs] (par rapport à l'état initial)
   - la taille des éléments internes de [qs]
*/
/* -------------------------------------------------------------------------- */

/*@ requires \true;   // à compléter
  @
  @ assigns \nothing; // à compléter
  @
  @ behavior full: // [qs] est complet
  @   ensures \true;  // à compléter
  @
  @ behavior space_left: // la file de [qs] a au moins un espace libre
  @   ensures \true; // à compléter
  
  @ behavior transfer: // la file de [qs] est complète, mais pas sa pile
  @   ensures \true; // à compléter
  @   ensures // ce début est cadeau
  @     \let size = MAX_SIZE - \at(qs->stack.size, Pre);
  @     \let offset = size % 2 == 0 ? size / 2 : size / 2 + 1;
  @     \true;
  
  @ complete behaviors;
  @ disjoint behaviors;
  @ */
int enqueue(qstack *qs, elt e) {
    if (! transfer(&qs->queue, &qs->stack))
	return -1;
    qs->queue.content[qs->queue.size] = e;
    qs->queue.size++; 
    return e;
}
