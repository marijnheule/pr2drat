/***************************************************************************************[pr2drat.c]
Copyright (c) 2017-2020 Marijn Heule, Carnegie Mellon University
Last edit, September 6, 2020

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <stdio.h>
#include <stdlib.h>

int main (int argc, char** argv) {
  int i, nVar, nCls, opt = 0;

  FILE* cnf = fopen (argv[1], "r");
  if (cnf == NULL) {
    printf ("c ERROR parsing CNF formula %s\n", argv[1]);
    exit (0); }

  char comment[1024];

  int tmp = fscanf (cnf, " p cnf %i %i ", &nVar, &nCls);
  while (tmp < 2) {
    tmp = fscanf (cnf, " %s ", comment);
    tmp = fscanf (cnf, " p cnf %i %i ", &nVar, &nCls);
  }

  // parse cnf
  int lit, nLit = 0, *formula;
  formula = (int*) malloc (sizeof (int) * nVar * nCls); // should become something dynamic
  while (1) {
    tmp = fscanf (cnf, " %i ", &lit);
    if (tmp == EOF) break;
    formula[nLit++] = lit; }

  fclose (cnf);

  if (argv[3] != NULL)
    if (argv[3][0] == '-' && argv[3][1] == 'O') opt = 1;

  FILE *pr  = fopen (argv[2], "r");
  if (pr == NULL) {
    printf ("c ERROR parsing PR proof %s\n", argv[2]);
    exit (0); }

  int *assignment;
  assignment  = (int*) malloc (sizeof (int) * (2*nVar + 1));
  assignment += nVar;
  int def = nVar + 1;
  int *lemma, lemma_size, *witness, witness_size;

  lemma   = (int*) malloc (sizeof (int) * nVar);
  witness = (int*) malloc (sizeof (int) * nVar);

  while (1) {
    tmp = fscanf (pr, " d %i ", &lit);
    if (tmp == EOF) break;

    // assignment reset... should become redundant
    for (i = 1; i <= nVar; i++) assignment[i] = assignment[-i] = 0;

    // if deletion step, then output step to stdout
    // and remove the clause from the formula.
    if (tmp > 0) {
      int toMatch = 1;
      if (abs(lit) > nVar) {
        printf ("c introduction of new variables in not supported\n");
        exit (0); }
      assignment[lit] = 1;
      printf ("d %i ", lit);
      while (lit) {
        tmp = fscanf (pr, " %i ", &lit);
        if (abs(lit) > nVar) {
          printf ("c introduction of new variables in not supported\n");
          exit (0); }
        if (lit != 0) printf ("%i ", lit), assignment[lit] = 1, toMatch++;
        else          printf ("0\n"); }

      int first = 0;
      for (i = 0; i < nLit; i++) {
        if (formula[i] == 0 && (i - first) == toMatch) {
          int k;
//          printf ("c deleting: "); for (k = first; k < i; k++) printf ("%i ", formula[k]); printf ("0\n");
          for (k = first; k < i; k++) formula[k] = 0;
          goto next_lemma; }
        if (assignment[formula[i]] != 1) {
          while (formula[i] != 0) i++;
          first = i + 1; } }
      goto next_lemma; }
    else { // parse lemma and potential witness
      int wflag    = 0;
      lemma_size   = 0;
      witness_size = 0;
      tmp = fscanf (pr, " %i ", &lit);
      if (abs(lit) > nVar) {
        printf ("c introduction of new variables in not supported\n");
        exit (0); }
      int pivot    = lit;
      lemma[lemma_size++] = lit;
      while (lit) {
        tmp = fscanf (pr, " %i ", &lit);
        if (abs(lit) > nVar) {
          printf ("c introduction of new variables in not supported\n");
          exit (0); }
        if (lit == pivot) {
          wflag = 1;
          lemma[lemma_size++] = 0; }
        if (wflag) witness[witness_size++] = lit;
        else       lemma  [  lemma_size++] = lit; }

      int *p;
      // if no witness is provided, then the lemma should be DRAT already
      if (witness_size == 0) {
        p = lemma;
        while (*p) printf ("%i ", *p++);
        printf ("0\n");
        p = lemma;
        while (*p) formula[nLit++] = *p++;
        formula[nLit++] = 0;
        goto next_lemma; }

      // set the assignment to the witness
      p = witness;
      while (*p) { lit = *p++; assignment[ lit] =  2; assignment[-lit] = -2; }

      int forced = 0, count = 0;

      if (opt) {
        for (i = 0; i < nLit; i++) {
          if (formula[i] == 0) { // end of clause
            if ((count == 1) && (assignment[forced] == 2)) {
              assignment[ forced] =  1;
              assignment[-forced] = -1; }
            forced = 0; count = 0; }
          else if (assignment[formula[i]] != -2) { count++; forced = formula[i];  } } }

      int mflag = 1;
      p = lemma;
      while (*p) if (assignment[*p++] == 2) mflag = 0;

      count = 0;
      p = lemma;
      while (*p++) count++;
      if (count == 1) mflag = 0;

//      mflag = 0;

//      printf("c mflag = %i\n", mflag);

      // phase I: add shortened copies of clauses reduced, but not satisfied by omega
      int piv = 0, sat = 0, red = 0;
      if (mflag == 0) {
              int k;
        for (i = 0; i < nLit; i++) {
          if (formula[i] == 0) {
            if ((sat == 0) && (red >  0)) {
              printf ("%i ", -def);
              for (k = piv; k < i; k++)
                if (assignment[formula[k]] == 0)
                  printf ("%i ", formula[k]);
              printf("0\n"); }
            piv = i + 1; sat = 0; red = 0; }
          else if (assignment[formula[i]] >  0) sat++;
          else if (assignment[formula[i]] < -1) red++; } }
      else {
        p = lemma;
        while (*p) printf ("%i %i 0\n", -def, -(*p++));
      }

      // phase II (a): add the implication x -> omega
      if (opt == 0 && mflag == 0) {
        p = witness;
        while (*p) printf ("%i %i 0\n", -def, *p++); }

      // phase II (b): weaken the involved clauses
      piv = 0, sat = 0, red = 0;
      for (i = 0; i < nLit; i++) {
        if (formula[i] == 0) {
          if ((sat > 0) && (red >  0)) {
            int k;
            printf ("%i ", def);
            for (k = piv; k < i; k++) printf ("%i ", formula[k]);
            printf("0\n");
            printf ("d ");
            for (k = piv; k < i; k++) printf ("%i ", formula[k]);
            printf("0\n"); }
          piv = i + 1; sat = 0; red = 0; }
        else if (assignment[formula[i]] >  0) sat++;
        else if (assignment[formula[i]] < -1) red++; }

      // phase II (c): remove the implication x -> omega
      if (opt == 0 && mflag == 0) {
        p = witness;
        while (*p) printf ("d %i %i 0\n",  *p++, -def); }

      // phase III: print the weakened PR clause
      p = lemma;
      printf ("%i ", def);
      while (*p) printf ("%i ", *p++);
      printf ("0\n");

      // phase IV (a): add the implication x -> omega
      p = witness;
      while (*p) {
        int lit = *p++;
        if (assignment[lit] == 2) printf ("%i %i 0\n", lit, -def); }
      if (mflag == 0) {
        p = witness;
        while (*p) {
          int lit = *p++;
          if (assignment[lit] == 1) printf ("%i %i 0\n", lit, -def); } }
      else {
        p = lemma;
        while (*p) printf ("d %i %i 0\n", -def, -(*p++));
      }

      // phase IV (b): strengthen the involved clauses
      piv = 0, sat = 0, red = 0;
      for (i = 0; i < nLit; i++) {
        if (formula[i] == 0) {
          if ((sat > 0) && (red >  0)) {
            int k;
            for (k = piv; k < i; k++) if (assignment[formula[k]] == 1) printf ("%i ", formula[k]);
            for (k = piv; k < i; k++) if (assignment[formula[k]] != 1) printf ("%i ", formula[k]);
            printf("0\n");
            printf ("d %i ", def);
            for (k = piv; k < i; k++) printf ("%i ", formula[k]);
            printf("0\n"); }
          piv = i + 1; sat = 0; red = 0; }
        else if (assignment[formula[i]] >  0) sat++;
        else if (assignment[formula[i]] < -1) red++; }

      // strengthen the weakened PR clause and add it to the formula
      p = lemma;
      while (*p) printf ("%i ", *p++);
      printf ("0\n");
      p = lemma;
      printf ("d %i ", def);
      while (*p) printf ("%i ", *p++);
      printf ("0\n");
      p = lemma;
      while (*p) formula[nLit++] = *p++;
      formula[nLit++] = 0;

      // phase IV (c): remove the implication x -> omega
      p = witness;
      while (*p) {
        int lit = *p++;
        if (assignment[lit] == 2) printf ("d %i %i 0\n", lit, -def); }
      if (mflag == 0) {
        p = witness;
        while (*p) {
          int lit = *p++;
          if (assignment[lit] == 1) printf ("d %i %i 0\n", lit, -def); } }

      // phase IV: remove the clauses that contain the literal -x (which are blocked)
      if (mflag == 0) {
        piv = 0, sat = 0, red = 0;
        for (i = 0; i < nLit; i++) {
          if (formula[i] == 0) {
            if ((sat == 0) && (red >  0)) {
              int k;
              printf ("d %i ", -def);
              for (k = piv; k < i; k++)
                if (assignment[formula[k]] == 0)
                  printf ("%i ", formula[k]);
                printf("0\n"); }
            piv = i + 1; sat = 0; red = 0; }
          else if (assignment[formula[i]] >  0) sat++;
          else if (assignment[formula[i]] < -1) red++; } }

    next_lemma:; }
  }
}
