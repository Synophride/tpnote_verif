/* -------------------------------------------------------------------------- */
/*
  Ce fichier implémente une structure de données, appelée qstack, permettant
  d'accéder rapidement au dernier élément ajouté (comme une pile LIFO), mais
  permettant d'ajouter aussi facilement un élément à la fin (comme une file
  FIFO). Pour cela, sa représentation interne est composée d'une pile et d'une
  file, représentées ici par des tableaux.
  
  Votre but est de:

  1. prouver l'absence d'erreurs à l'exécution de toutes les fonctions
  (en ajoutant les préconditions ACSL nécessaires) ; il est conseillé de 
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
  @       
  @   predicate queueHasShifted{L1,L2}(xifo *queue, integer offset) =
  @     \forall integer i; 0 <= i < \at(queue->size, L1) - 1 ==>
  @       \at(queue->content[i], L1) == \at(queue->content[i+offset], L2); 
  @       
  @   predicate isTransferred{L1,L2}
  @     (xifo *stack, xifo *queue, integer offset) =
  @     \forall integer i; 0 <= i < offset ==>
  @       \at(stack->content[offset-i-1], L1) == \at(queue->content[i], L2);
  @ } */

/* -------------------------------------------------------------------------- */
/* [pop(qs)] enlève le sommet de la pile.

   La spécification formelle doit notamment préciser, pour chaque comportement:
   - le résultat retourné
   - la taille des éléments internes de [qs]
   - le contenu des éléments internes de [qs] (par rapport à l'état initial)
 */
/* -------------------------------------------------------------------------- */

/*@ requires \true;   // à compléter
  @
  @ assigns \nothing; // à compléter
  @
  @ behavior empty:       // cas d'une qstack vide
      ensures \true;  // à compléter
  @
  @ behavior stack_empty: // cas où seule la pile interne est vide
      ensures \true;  // à compléter
  @
  @ behavior filled:      // cas où ni la pile, ni la file ne sont vides
      ensures \true;  // à compléter
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @ */
int pop(qstack *qs) {
  if (qs->stack.size == 0) {
    if (qs->queue.size == 0)
      return -1;
    qs->queue.size--;
    int res = qs->queue.content[0];
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

   La spécification formelle doit notamment préciser, pour chaque comportement:
   - le résultat retourné
   - la taille des éléments internes de [qs]
   - le contenu des éléments internes de [qs] (par rapport à l'état initial)
*/
/* -------------------------------------------------------------------------- */

/*@ requires \true;   // à compléter
  @ requires \separated(src, dst); // celui-là, c'est cadeau :-)
  @
  @ assigns \nothing; // à compléter
  @
  @ behavior full: // [src] et [dst] sont complets
  @   ensures \true;  // à compléter
  @
  @ behavior space_left: // [src] a au moins un espace libre
  @   ensures \true; // à compléter
  @
  @ behavior transfer: // [src] est complet, mais pas [dst]
  @   ensures \true; // à compléter
  @   ensures // ce début est cadeau
  @     \let size = MAX_SIZE - \at(dst->size, Pre);
  @     \let offset = size % 2 == 0 ? size / 2 : size / 2 + 1;
  @     \true;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @ */
int transfer(xifo *src, xifo *dst) {
  if (src->size == MAX_SIZE) {
    if (dst->size == MAX_SIZE)
      return 0;
    else {
      int size = MAX_SIZE - dst->size;
      int offset = size % 2 == 0 ? size / 2 : size / 2 + 1;
      int i;
      for(i = dst->size-1; i >= 0; i--)
        dst->content[i+offset] = dst->content[i];
      for(i = 0; i < offset; i++)
        dst->content[i] = src->content[offset-i-1];
      for(i = 0; i < src->size-offset; i++)
        src->content[i] = src->content[i+offset];
      src->size -= offset;
      dst->size += offset;
      /* les assertions suivantes sont nécessaires avec certaines versions de
         Frama-C et Alt-Ergo. Elles doivent être prouvées. */
      /*@ assert queueHasShifted{Pre,Here}(dst, offset); */
      /*@ assert isTransferred{Pre,Here}(src, dst, offset); */
      /*@ assert stackHasShifted{Pre,Here}(src, offset); */
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
  @
  @ behavior transfer: // la file de [qs] est complète, mais pas sa pile
  @   ensures \true; // à compléter
  @   ensures // ce début est cadeau
  @     \let size = MAX_SIZE - \at(qs->stack.size, Pre);
  @     \let offset = size % 2 == 0 ? size / 2 : size / 2 + 1;
  @     \true;
  @
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
