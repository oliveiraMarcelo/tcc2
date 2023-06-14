/*********************************************************************
 * (C) Copyright 1999 Albert Ludwigs University Freiburg
 *     Institute of Computer Science
 *
 * All rights reserved. Use of this software is permitted for 
 * non-commercial research purposes, and it may be copied only 
 * for that use.  All copies must include this copyright message.
 * This software is made available AS IS, and neither the authors
 * nor the  Albert Ludwigs University Freiburg make any warranty
 * about the software or its performance. 
 *********************************************************************/

/*********************************************************************
 * File: backdoors.c
 * Description: functions for cnf output
 *
 * Author: Joerg Hoffmann 2003
 *  Modified: Shane Neph 2004 and 2006
 *********************************************************************/

#include "bb.h"

#include "output.h"
#include "memory.h"

#include "instantiateI.h"
#include "instantiateII.h"

#include "graph.h"

#include "cnfout.h"

# include<stdio.h>
# include<time.h>
int **lcode;

int **lclause;
int *lclause_size;
int lnum_clauses;

int *lop_to_code;
int *ltime_to_code;
extern const int UNSAT;
extern const int SAT;

/* Razer - 28/01/2012
   Esta macro serve para trocar a polaridade da ação, com o intuito
   de gerar MHF */
#define GET_ACTION_PROP(x)   (-x)

/* Razer - Para gerar MHF*/
int get_action_prop(int x) {
	if (gcmd_line.makeMHF == 1) {
		return GET_ACTION_PROP(x);
	}
	else {
		return x;
	}
}

void do_cnf_output(int create)

{
	if (gcmd_line.cnfout == 1) {
		if (gcmd_line.makeMHF == 1)
			print_action_based_encoding_MHF(gcmd_line.cnflayer, create);
		else
			if (gcmd_line.makePBS == 1)
				print_action_based_encoding_PBS(gcmd_line.cnflayer, create);
			else {
			    if (gcmd_line.makePBS == 2)
				    print_action_based_encoding_PBS2(gcmd_line.cnflayer, create); /* nao alterei nada nesta func. */
                else         
				    print_action_based_encoding(gcmd_line.cnflayer, create);
            }
		return;
	}

	if (gcmd_line.cnfout == 2) {
		print_gpstyle_action_based_encoding(gcmd_line.cnflayer, create);
		return;
	}

	if (gcmd_line.cnfout == 3) {
		print_gp_based_encoding(gcmd_line.cnflayer, create);
		return;
	}

    /* este eh a chamada default do SatPlan (quando o encoding nao eh passado) */
	if (gcmd_line.cnfout == 4) {
	    if (gcmd_line.makePBS == 2)
		   print_thin_gp_based_encoding_PBS2(gcmd_line.cnflayer, create);
        else
		   print_thin_gp_based_encoding(gcmd_line.cnflayer, create);
		return;
	}

	printf("\n\nEXIT: cnf out %d not implemented\n\n", gcmd_line.cnfout);
	exit(1);
}


/* action-based
 * Razer
 *    The same code of print_action_based_encoding, but with ifs to genenare MHF
 */
void print_action_based_encoding_MHF(int layer, int create)

{
	FILE *CNF, *VARFILE;

	int i, j, t, k, ft, op, prevcl, l;
	int *F, *A;
	int code;
	int tmpNumber;

	int nGclauses = 0, nAclauses = 0, nEclauses = 0;

	lclause = (int **) calloc(MAX_CLAUSES, sizeof(int *));
	lclause_size = (int *) calloc(MAX_CLAUSES, sizeof(int));
	lcode = (int **) calloc(layer, sizeof(int *));
	lop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ltime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i < layer; i++) {
		lcode[i] = (int *) calloc(gnum_op_conn, sizeof(int));
		for (j = 0; j < gnum_op_conn; j++) {
			lcode[i][j] = -1;
		}
	}

	F = (int *) calloc(gnum_ft_conn, sizeof(int));
	for (i = 0; i < gnum_ft_conn; i++) {
		F[i] = -1;
	}
	/* no-ops are included in the gop_conn!
	 */
	A = (int *) calloc(gnum_op_conn, sizeof(int));
	for (i = 0; i < gnum_op_conn; i++) {
		A[i] = -1;
	}

	/* layer 0
	 */
	for (i = 0; i < ginitial_state.num_F; i++) {
		F[ginitial_state.F[i]] = 0;
	}

	printf("\n\ncreating action-based encoding...");

	/* prec constraints, + code assignment.
	 */
	lnum_clauses = 0;
	code = 1; /* variables numbered 1 .. n */
	printf("\nbuilding rplan graph layers --> up to layer %d...", layer);
	for (t = 0; t < layer; t++) {
		for (i = 0; i < gnum_op_conn; i++) {
			/* Razer - buffer de acao i é -1 */
			if (A[i] == -1) {

				/* Razer - Para todas as pre-condicoes do operador i ... */
				for (j = 0; j < gop_conn[i].num_P; j++) {
					if (F[gop_conn[i].P[j]] == -1 || F[gop_conn[i].P[j]] > t)
						break;
				}
				if (j < gop_conn[i].num_P)
					continue;
				/* now i is an op that comes in here.
				 */
				/* Razer - O laco acima varreu F e os indices
				 sao ou -1 ou > t (layer) */

				/* Razer - buffer de acao i é t (o layer) */
				A[i] = t;
				if (0) {
					printf("\nA %d at %d", i, t);
				}
				/* mark its add effects.
				 */
				/* Razer - Para todos os efeitos (add) da operacao i
				 marca em F para o proximo layer */
				for (j = 0; j < gop_conn[i].num_A; j++) {
					ft = gop_conn[i].A[j];
					if (F[ft] != -1)
						continue;
					F[ft] = t + 1;
				}
			}

			/* Razer - neste ponto, o buffer A contem as
			 acoes disparadas neste layer e F contem os
			 fatos adicionados (proximo layer) */

			/* insert prec clauses, if at t > 0.
			 */
			/* Razer - se for o primeiro layer, nao tem
			 precondicao */
			if (t == 0) {
				continue;
			}

			/* Razer - vai setar as precondicoes
			 Para todas as precondicoes da acao i... */
			for (j = 0; j < gop_conn[i].num_P; j++) {
				/* Razer - obtem o fato que eh precondicao */
				ft = gop_conn[i].P[j];

				if (lnum_clauses == MAX_CLAUSES) {
					printf(
							"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}

				/* Razer - aloca uma clausula para esta precondicao
				 O tamanho da clausula eh o numero de operadores dos quais
				 este fato eh add */
				lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A + 1,
						sizeof(int));
				/* here the op i is used at t, for the 1st time. assign the code.
				 */
				if (j == 0) {
					if (lcode[t][i] != -1) {
						printf(
								"\n\nEXIT: op code %d at %d already assigned??\n\n",
								i, t);
						exit(1);
					}
					if (0) {
						printf("\nC %d at %d", i, t);
					}
					/* Razer - guarda em lcode [layer][operador] o valor code
					 code guarda numeracao sequencial de variaveis */
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					/* Razer - lop_to_code e ltime_to_code servem para
					 fazer referencia reversa com lcode
					 lop_to_code [ variavel ]  - retorna o operador
					 ltime_to_code [ variavel ] - retorna o layer */
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}

				/* Razer - Primeira variavel da clausula eh a acao i do layer t
				 Nega o operador (se nao for MHF)
				 TODO OK colocar um if para gerar MHF */
				if (gcmd_line.makeMHF == 1)
					lclause[lnum_clauses][0] = lcode[t][i];
				else
					lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				lclause_size[lnum_clauses] = 1;

				/* Razer - Para todas as operacoes para as quais
				 o fato ft eh add ... */
				for (k = 0; k < gft_conn[ft].num_A; k++) {

					/* Razer - retorna uma operacao para a qual o
					 fato ft eh add... */
					op = gft_conn[ft].A[k];
					if (A[op] == -1 || A[op] > t - 1) {
						continue;
					}
					/* Razer - Se no layer anterior esta
					 operacao nao esta marcada... */
					if (lcode[t - 1][op] == -1) {
						/* Razer - Marca a operacao */
						lcode[t - 1][op] = code++;
						if (0) {
							printf("\npC %d at %d", op, t - 1);
						}
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t - 1;
					}
					/* Razer - acrescenta a operacao as clausulas
					 TODO OK adicionar um IF para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
								(-1) * lcode[t - 1][op];
					else
						lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
								lcode[t - 1][op];
				}
				if (lclause_size[lnum_clauses] == 1) {
					printf("\n\nEXIT: no achiever in at t>0??\n\n");
					exit(1);
				}
				nAclauses++;
				lnum_clauses++;
			} /* pres of i-op */
		} /* i -- op */
	} /* t */

	/* goal constraints
	 */
	printf("\ngoal constraints...");
	for (i = 0; i < ggoal_state.num_F; i++) {
		ft = ggoal_state.F[i];

		if (lnum_clauses == MAX_CLAUSES) {
			printf("\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
			exit(1);
		}
		lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A, sizeof(int));
		lclause_size[lnum_clauses] = 0;
		for (k = 0; k < gft_conn[ft].num_A; k++) {
			op = gft_conn[ft].A[k];
			if (A[op] == -1 || A[op] > layer - 1) {
				continue;
			}
			if (lcode[layer - 1][op] == -1) {
				lcode[layer - 1][op] = code++;
				if (code == MAX_CNF_VARS + 1) {
					printf(
							"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
					exit(1);
				}
				lop_to_code[code - 1] = op;
				ltime_to_code[code - 1] = layer - 1;
			}
			/* TODO OK Colocar um IF aqui para gerar MHF */
			if (gcmd_line.makeMHF == 1)
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
						(-1) * lcode[layer - 1][op];
			else
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
						lcode[layer - 1][op];
		}
		if (lclause_size[lnum_clauses] == 0) {
			printf("\n\nno achiever in for goal?? deadline too low!\n\n");
			exit(UNSAT);
		}
		lnum_clauses++;
		nGclauses++;
	} /* goals */

	/* exclusion constraints. implementation a bit smart, to avoid
	 * time-consuming all-op-pairs-check.
	 */
	printf("\nbuilding exclusion constraints --> up to layer %d...", layer);
	for (t = 0; t < layer; t++) {
		for (i = 0; i < gnum_op_conn; i++) {
			if (A[i] == -1 || A[i] > t)
				continue;
			prevcl = lnum_clauses;
			for (j = 0; j < gop_conn[i].num_D; j++) {
				ft = gop_conn[i].D[j];
				for (k = 0; k < gft_conn[ft].num_P; k++) {
					op = gft_conn[ft].P[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							/* Razer - precisa ajustar este IF
							 * TODO OK colocar um IF para MHF
							 */
							if (gcmd_line.makeMHF == 1) {
								if ( (-1) * lclause[l][1] == (-1) * lcode[t][op])
									break;
							}
							else {
								if (lclause[l][1] == (-1) * lcode[t][op])
									break;
							}
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh uma operacao
					 TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];

					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}

					/* TODO OK colocar um IF aqui para gerar o MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] =  lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];

					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is pre of */

				for (k = 0; k < gft_conn[ft].num_A; k++) {
					op = gft_conn[ft].A[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							/* Razer - Tem que ajustar este IF para MHF
							 * TODO OK colocar um if para MHF
							 */
							if (gcmd_line.makeMHF == 1) {
								if ((-1) * lclause[l][1] == (-1) * lcode[t][op])
									break;
							}
							else {
								if (lclause[l][1] == (-1) * lcode[t][op])
									break;
							}
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - Ajustar
					 * TODO OK Adicionar um IF para gerar MHF
					 */
					if (gcmd_line.makeMHF == 1) {
						lclause[lnum_clauses][0] = lcode[t][i];
					}
					else {
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					}
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] =  lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is added by */
			} /* j: fts that i dels */

			for (j = 0; j < gop_conn[i].num_P; j++) {
				ft = gop_conn[i].P[j];
				for (k = 0; k < gft_conn[ft].num_D; k++) {
					op = gft_conn[ft].D[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							/* Razer - Ajustar este if para MHF
							 * TODO OK Colocar um IF para gerar MHF
							 */
							if (gcmd_line.makeMHF == 1) {
								if ((-1) * lclause[l][1] == (-1) * lcode[t][op])
									break;
							}
							else {
								if (lclause[l][1] == (-1) * lcode[t][op])
									break;
							}
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh um operador
					 TODO OKK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] =  lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is del by */
			} /* j: fts that i has as prec */

			for (j = 0; j < gop_conn[i].num_A; j++) {
				ft = gop_conn[i].A[j];
				for (k = 0; k < gft_conn[ft].num_D; k++) {
					op = gft_conn[ft].D[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							/* Razer - Ajustar este if para MHF
							 * TODO OK Colocar um IF para gerar MHF
							 */
							if (gcmd_line.makeMHF == 1) {
								if ((-1) * lclause[l][1] == (-1) * lcode[t][op])
									break;
							}
							else {
								if (lclause[l][1] == (-1) * lcode[t][op])
									break;
							}
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh um operador
					 TODO OK Colocar um IF aqui para gerar MHF*/
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] =  lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is del by */
			} /* j: fts that i adds */
		} /* i: ops at t */
	} /* t */

	/* that's it. print CNF file.
	 */
	if (gcmd_line.debug) {
		if ((VARFILE = fopen(gcmd_line.varFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open VARFILE file.\n\n");
			exit(1);
		}
		fprintf(VARFILE, "\n\nc DECISION LAYER %d, ACTION-BASED ENCODING.",
				layer);
		fprintf(VARFILE, "\n\nc VARS:");

		for (i = 1; i < code; i++) {
			fprintf(VARFILE, "\nc var %2d action (", i);
			print_op_nameToFile(lop_to_code[i], VARFILE);
			fprintf(VARFILE, ") %d", ltime_to_code[i]);
		}
		/*
		 fprintf(VARFILE, "\n\nCLAUSES:");
		 for ( i = 0; i < lnum_clauses; i++ ) {
		 for ( j = 0; j < lclause_size[i]; j++ ) {
		 if ( lclause[i][j] > 0 ) {
		 fprintf(VARFILE, "\n%6d - ", i);
		 fprintf(VARFILE, "(");
		 print_op_nameToFile( lop_to_code[lclause[i][j]], VARFILE );
		 fprintf(VARFILE, " at %d) VAR = %d", ltime_to_code[lclause[i][j]], lclause[i][j] );
		 } else {
		 fprintf(VARFILE, "\n%6d - ", i);
		 fprintf(VARFILE, "(NOT ");
		 print_op_nameToFile( lop_to_code[(-1)*lclause[i][j]], VARFILE );
		 fprintf(VARFILE, " at %d) VAR = %d", ltime_to_code[(-1)*lclause[i][j]], lclause[i][j] );
		 }
		 }
		 }
		 fprintf(VARFILE, "0\n");
		 */
		fclose(VARFILE);
	}

	printf(
			"\n\nDECISION LAYER %d, WRITING ACTION-BASED ENCODING WITH %d VARS, %d CLAUSES.",
			layer, code - 1, lnum_clauses);
	printf("\n%d G clauses, %d A clauses, %d E clauses.", nGclauses, nAclauses,
			nEclauses);

	if (create == 0) {
		if ((CNF = fopen(gcmd_line.cnfFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open CNF file.\n\n");
			exit(1);
		}

		fprintf(CNF,
				"c CNF file planning task -p %s, -o %s, -f %s, bound %d, action based encoding\n",
				gcmd_line.path, gcmd_line.ops_file_name,
				gcmd_line.fct_file_name, layer);
		printf("\nb-check %d\n", gcmd_line.binary_clause_only);
		tmpNumber = lnum_clauses;
		if (gcmd_line.binary_clause_only != 0) {
			for (i = 0; i < tmpNumber; ++i) {
				if (lclause_size[i] > 2)
					--lnum_clauses;
			}
		}

		if (gcmd_line.makeMHF == 1) {

			if (gcmd_line.makePURE == 1) {
				/* TODO fazer o calculo dos literais enquanto gera as clausulas, para ser
				 mais rapido */

				char* vec_2cnf = (char*)malloc((code+1) * sizeof(char));
				char* vec_horn = (char*)malloc((code+1) * sizeof(char));
				char* vec_unit = (char*)malloc((code+1) * sizeof(char));

				memset(vec_2cnf, 0, (code+1));
				memset(vec_horn, 0, (code+1));
				memset(vec_unit, 0, (code+1));

				printf("start analysing\n");

				for (i = 0; i < tmpNumber; i++) {
					if (lclause_size[i] == 2) {
						/* binary - 2cnf - monotone - positive */
						for (j = 0; j < lclause_size[i]; j++) {
							int x = abs(lclause[i][j]);
							vec_2cnf[x] = 1;
						}
					}
					else if (lclause_size[i] > 2) {
						/* Horn */
						for (j = 0; j < lclause_size[i]; j++) {
							int x = abs(lclause[i][j]);
							vec_horn[x] = 1;
						}
					}
					else if (lclause_size[i] == 1) {
						/* Unit */
						for (j = 0; j < lclause_size[i]; j++) {
							int x = abs(lclause[i][j]);
							vec_unit[x] = 1;
						}
					}
				}
				printf("start generating\n");
				for (i=1; i<=code; i++) {
					/* printf("   var: %d h[%d] 2[%d] u[%d]\n", i, vec_horn[i], vec_2cnf[i], vec_unit[i]); */
					if (vec_unit[i]==1) {
						/* eh unitaria */
						continue;
					}
					else {
						if (vec_horn[i]==1 && vec_2cnf[i]==0) {
							/* So aparece na horn */
							lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
							lclause[lnum_clauses][0] = -1 * i;
							lclause_size[lnum_clauses] = 1;
							lnum_clauses++;
							printf("\n Add %d\n", -i);
						}
						else if (vec_horn[i]==0 && vec_2cnf[i]==1) {
							/* So aparece na 2cnf */
							lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
							lclause[lnum_clauses][0] = i;
							lclause_size[lnum_clauses] = 1;
							lnum_clauses++;
							printf("\n Add %d\n", i);
						}
					}

				}
			}
			printf("start writing\n");

			fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);
			for (i = 0; i < lnum_clauses; i++) {
				for (j = 0; j < lclause_size[i]; j++) {
					fprintf(CNF, "%d ", lclause[i][j]);
				}
				fprintf(CNF, "0\n");
			}
		}
		else {
				if (gcmd_line.makePBS == 1) {
						fprintf(CNF, "* #variable= %d #constraint= %d\n", code - 1, lnum_clauses);
						for (i = 0; i < tmpNumber; i++) {
								if (gcmd_line.binary_clause_only == 0 || lclause_size[i] < 3) {
										for (j = 0; j < lclause_size[i]; j++) {
												if (lclause[i][j] < 0)
														fprintf(CNF, "+1 ~x%d ", -1*lclause[i][j]);
												else
														fprintf(CNF, "+1 x%d ", lclause[i][j]);
										}
										fprintf(CNF, " >= 1;\n");
								}
						}
						fclose(CNF);
				}
				else {
						fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);
						for (i = 0; i < tmpNumber; i++) {
								if (gcmd_line.binary_clause_only == 0 || lclause_size[i] < 3) {
										for (j = 0; j < lclause_size[i]; j++) {
												fprintf(CNF, "%d ", lclause[i][j]);
										}
										fprintf(CNF, "0\n");
								}
						}
						fclose(CNF);
				}
		}
	}
}


/* action-based PBS
   Razer e Bruno
 */
void print_action_based_encoding_PBS(int layer, int create)

{
	FILE *CNF, *VARFILE;

	int i, j, t, k, ft, op, prevcl, l;
	int *F, *A;
	int code;
	int tmpNumber;

	int nGclauses = 0, nAclauses = 0, nEclauses = 0;

	lclause = (int **) calloc(MAX_CLAUSES, sizeof(int *));
	lclause_size = (int *) calloc(MAX_CLAUSES, sizeof(int));
	lcode = (int **) calloc(layer, sizeof(int *));
	lop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ltime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i < layer; i++) {
		lcode[i] = (int *) calloc(gnum_op_conn, sizeof(int));
		for (j = 0; j < gnum_op_conn; j++) {
			lcode[i][j] = -1;
		}
	}

	F = (int *) calloc(gnum_ft_conn, sizeof(int));
	for (i = 0; i < gnum_ft_conn; i++) {
		F[i] = -1;
	}
	/* no-ops are included in the gop_conn!
	 */
	A = (int *) calloc(gnum_op_conn, sizeof(int));
	for (i = 0; i < gnum_op_conn; i++) {
		A[i] = -1;
	}

	/* layer 0
	 */
	for (i = 0; i < ginitial_state.num_F; i++) {
		F[ginitial_state.F[i]] = 0;
	}

	printf("\n\ncreating action-based encoding...");

	/* prec constraints, + code assignment.
	 */
	lnum_clauses = 0;
	code = 1; /* variables numbered 1 .. n */
	printf("\nbuilding rplan graph layers --> up to layer %d...", layer);
	for (t = 0; t < layer; t++) {
		for (i = 0; i < gnum_op_conn; i++) {
			/* Razer - buffer de acao i é -1 */
			if (A[i] == -1) {

				/* Razer - Para todas as pre-condicoes do operador i ... */
				for (j = 0; j < gop_conn[i].num_P; j++) {
					if (F[gop_conn[i].P[j]] == -1 || F[gop_conn[i].P[j]] > t)
						break;
				}
				if (j < gop_conn[i].num_P)
					continue;
				/* now i is an op that comes in here.
				 */
				/* Razer - O laco acima varreu F e os indices
				 sao ou -1 ou > t (layer)

				 Razer - buffer de acao i é t (o layer) */
				A[i] = t;
				if (0) {
					printf("\nA %d at %d", i, t);
				}
				/* mark its add effects.
				 */
				/* Razer - Para todos os efeitos (add) da operacao i
				 marca em F para o proximo layer */
				for (j = 0; j < gop_conn[i].num_A; j++) {
					ft = gop_conn[i].A[j];
					if (F[ft] != -1)
						continue;
					F[ft] = t + 1;
				}
			}

			/* Razer - neste ponto, o buffer A contem as
			 acoes disparadas neste layer e F contem os
			 fatos adicionados (proximo layer) */

			/* insert prec clauses, if at t > 0.
			 */
			/* Razer - se for o primeiro layer, nao tem
			 precondicao */
			if (t == 0) {
				continue;
			}

			/* Razer - vai setar as precondicoes
			 Para todas as precondicoes da acao i... */
			for (j = 0; j < gop_conn[i].num_P; j++) {
				/* Razer - obtem o fato que eh precondicao */
				ft = gop_conn[i].P[j];

				if (lnum_clauses == MAX_CLAUSES) {
					printf(
							"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}

				/* Razer - aloca uma clausula para esta precondicao
				 O tamanho da clausula eh o numero de operadores dos quais
				 este fato eh add */
				lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A + 1,
						sizeof(int));
				/* here the op i is used at t, for the 1st time. assign the code.
				 */
				if (j == 0) {
					if (lcode[t][i] != -1) {
						printf(
								"\n\nEXIT: op code %d at %d already assigned??\n\n",
								i, t);
						exit(1);
					}
					if (0) {
						printf("\nC %d at %d", i, t);
					}
					/* Razer - guarda em lcode [layer][operador] o valor code
					 code guarda numeracao sequencial de variaveis */
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					/* Razer - lop_to_code e ltime_to_code servem para
					 fazer referencia reversa com lcode
					 lop_to_code [ variavel ]  - retorna o operador
					 ltime_to_code [ variavel ] - retorna o layer */
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}

				/* Razer - Primeira variavel da clausula eh a acao i do layer t
				 Nega o operador (se nao for MHF)
				 TODO OK colocar um if para gerar MHF */
				if (gcmd_line.makeMHF == 1)
					lclause[lnum_clauses][0] =  lcode[t][i];
				else
					lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				lclause_size[lnum_clauses] = 1;

				/* Razer - Para todas as operacoes para as quais
				 o fato ft eh add ... */
				for (k = 0; k < gft_conn[ft].num_A; k++) {

					/* Razer - retorna uma operacao para a qual o
					 fato ft eh add... */
					op = gft_conn[ft].A[k];
					if (A[op] == -1 || A[op] > t - 1) {
						continue;
					}
					/* Razer - Se no layer anterior esta
					 operacao nao esta marcada... */
					if (lcode[t - 1][op] == -1) {
						/* Razer - Marca a operacao */
						lcode[t - 1][op] = code++;
						if (0) {
							printf("\npC %d at %d", op, t - 1);
						}
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t - 1;
					}
					/* Razer - acrescenta a operacao as clausulas
					 TODO OK adicionar um IF para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
								(-1) * lcode[t - 1][op];
					else
						lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
								lcode[t - 1][op];
				}
				if (lclause_size[lnum_clauses] == 1) {
					printf("\n\nEXIT: no achiever in at t>0??\n\n");
					exit(1);
				}
				nAclauses++;
				lnum_clauses++;
			} /* pres of i-op */
		} /* i -- op */
	} /* t */

	/* goal constraints
	 */
	printf("\ngoal constraints...");
	for (i = 0; i < ggoal_state.num_F; i++) {
		ft = ggoal_state.F[i];

		if (lnum_clauses == MAX_CLAUSES) {
			printf("\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
			exit(1);
		}
		lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A, sizeof(int));
		lclause_size[lnum_clauses] = 0;
		for (k = 0; k < gft_conn[ft].num_A; k++) {
			op = gft_conn[ft].A[k];
			if (A[op] == -1 || A[op] > layer - 1) {
				continue;
			}
			if (lcode[layer - 1][op] == -1) {
				lcode[layer - 1][op] = code++;
				if (code == MAX_CNF_VARS + 1) {
					printf(
							"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
					exit(1);
				}
				lop_to_code[code - 1] = op;
				ltime_to_code[code - 1] = layer - 1;
			}
			/* TODO OK Colocar um IF aqui para gerar MHF */
			if (gcmd_line.makeMHF == 1)
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
						(-1) * lcode[layer - 1][op];
			else
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
						lcode[layer - 1][op];
		}
		if (lclause_size[lnum_clauses] == 0) {
			printf("\n\nno achiever in for goal?? deadline too low!\n\n");
			exit(UNSAT);
		}
		lnum_clauses++;
		nGclauses++;
	} /* goals */

	/* exclusion constraints. implementation a bit smart, to avoid
	 * time-consuming all-op-pairs-check.
	 */
	printf("\nbuilding exclusion constraints --> up to layer %d...", layer);
	for (t = 0; t < layer; t++) {
		for (i = 0; i < gnum_op_conn; i++) {
			if (A[i] == -1 || A[i] > t)
				continue;
			prevcl = lnum_clauses;
			for (j = 0; j < gop_conn[i].num_D; j++) {
				ft = gop_conn[i].D[j];
				for (k = 0; k < gft_conn[ft].num_P; k++) {
					op = gft_conn[ft].P[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh uma operacao
					 TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}

					/* TODO OK colocar um IF aqui para gerar o MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] =  lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is pre of */
				for (k = 0; k < gft_conn[ft].num_A; k++) {
					op = gft_conn[ft].A[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is added by */
			} /* j: fts that i dels */

			for (j = 0; j < gop_conn[i].num_P; j++) {
				ft = gop_conn[i].P[j];
				for (k = 0; k < gft_conn[ft].num_D; k++) {
					op = gft_conn[ft].D[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh um operador
					 TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is del by */
			} /* j: fts that i has as prec */

			for (j = 0; j < gop_conn[i].num_A; j++) {
				ft = gop_conn[i].A[j];
				for (k = 0; k < gft_conn[ft].num_D; k++) {
					op = gft_conn[ft].D[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh um operador
					 TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];

					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is del by */
			} /* j: fts that i adds */
		} /* i: ops at t */
	} /* t */

	/* that's it. print CNF file.
	 */
	if (gcmd_line.debug) {
		if ((VARFILE = fopen(gcmd_line.varFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open VARFILE file.\n\n");
			exit(1);
		}
		fprintf(VARFILE, "\n\nc DECISION LAYER %d, ACTION-BASED ENCODING.",
				layer);
		fprintf(VARFILE, "\n\nc VARS:");

		for (i = 1; i < code; i++) {
			fprintf(VARFILE, "\nc var %2d action (", i);
			print_op_nameToFile(lop_to_code[i], VARFILE);
			fprintf(VARFILE, ") %d", ltime_to_code[i]);
		}
		/*
		 fprintf(VARFILE, "\n\nCLAUSES:");
		 for ( i = 0; i < lnum_clauses; i++ ) {
		 for ( j = 0; j < lclause_size[i]; j++ ) {
		 if ( lclause[i][j] > 0 ) {
		 fprintf(VARFILE, "\n%6d - ", i);
		 fprintf(VARFILE, "(");
		 print_op_nameToFile( lop_to_code[lclause[i][j]], VARFILE );
		 fprintf(VARFILE, " at %d) VAR = %d", ltime_to_code[lclause[i][j]], lclause[i][j] );
		 } else {
		 fprintf(VARFILE, "\n%6d - ", i);
		 fprintf(VARFILE, "(NOT ");
		 print_op_nameToFile( lop_to_code[(-1)*lclause[i][j]], VARFILE );
		 fprintf(VARFILE, " at %d) VAR = %d", ltime_to_code[(-1)*lclause[i][j]], lclause[i][j] );
		 }
		 }
		 }
		 fprintf(VARFILE, "0\n");
		 */
		fclose(VARFILE);
	}

	printf(
			"\n\nDECISION LAYER %d, WRITING ACTION-BASED ENCODING WITH %d VARS, %d CLAUSES.",
			layer, code - 1, lnum_clauses);
	printf("\n%d G clauses, %d A clauses, %d E clauses.", nGclauses, nAclauses,
			nEclauses);

	if (create == 0) {
		if ((CNF = fopen(gcmd_line.cnfFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open CNF file.\n\n");
			exit(1);
		}

		fprintf(CNF,
				"c CNF file planning task -p %s, -o %s, -f %s, bound %d, action based encoding\n",
				gcmd_line.path, gcmd_line.ops_file_name,
				gcmd_line.fct_file_name, layer);
		printf("\nb-check %d\n", gcmd_line.binary_clause_only);
		tmpNumber = lnum_clauses;
		if (gcmd_line.binary_clause_only != 0) {
			for (i = 0; i < tmpNumber; ++i) {
				if (lclause_size[i] > 2)
					--lnum_clauses;
			}
		}
		if (gcmd_line.makePBS == 1) {
				fprintf(CNF, "* #variable= %d #constraint= %d\n", code - 1, lnum_clauses);
				for (i = 0; i < tmpNumber; i++) {
						if (gcmd_line.binary_clause_only == 0 || lclause_size[i] < 3) {
								for (j = 0; j < lclause_size[i]; j++) {
										if (lclause[i][j] < 0)
												fprintf(CNF, "+1 ~x%d ", -1*lclause[i][j]);
										else
												fprintf(CNF, "+1 x%d ", lclause[i][j]);
								}
								fprintf(CNF, " >= 1;\n");
						}
				}
				fclose(CNF);
		}
		else {
	
			fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);
			for (i = 0; i < tmpNumber; i++) {
				if (gcmd_line.binary_clause_only == 0 || lclause_size[i] < 3) {
					for (j = 0; j < lclause_size[i]; j++) {
						fprintf(CNF, "%d ", lclause[i][j]);
					}
					fprintf(CNF, "0\n");
				}
			}
			fclose(CNF);
		}
		/* Razer - generate prefs */
		if (gcmd_line.makePREFS == 1) {
			/* the first variable or 2 CNF POSITIVE is generated as prefs.txt */
			FILE *prefs;

			char* vec_2cnf;
			vec_2cnf = (char*)malloc((MAX_CLAUSES) * sizeof(char));
			memset(vec_2cnf, 0, (MAX_CLAUSES));


			for (i = 0; i < tmpNumber; i++) {
				if (lclause_size[i] == 2) {
					/* binary - 2cnf - monotone - positive */
					for (j = 0; j < lclause_size[i]; j++) {
						int x = abs(lclause[i][j]);
						vec_2cnf[x] = 1;
					}
				}
			}


			if ((prefs = fopen("prefs.txt", "w")) == NULL ) {
				printf("\n\ncan't open PREFS file.\n\n");
				exit(1);
			}

			for (i=0; i<tmpNumber; i++) {
			   if (vec_2cnf[i]) {
			 		fprintf(prefs, "%d\n", i);
				}
			}
			fclose(prefs);
		}
	}
}

/* action-based PBS2 - compressão de formulas 7.1, 7.2 e 8
   Razer e Bruno
 */
void print_action_based_encoding_PBS2(int layer, int create)

{
	FILE *CNF, *VARFILE;

	int i, j, t, k, ft, op, prevcl, l;
	int *F, *A;
	int code;
	int tmpNumber;

	int nGclauses = 0, nAclauses = 0, nEclauses = 0;

	lclause = (int **) calloc(MAX_CLAUSES, sizeof(int *));
	lclause_size = (int *) calloc(MAX_CLAUSES, sizeof(int));
	lcode = (int **) calloc(layer, sizeof(int *));
	lop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ltime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i < layer; i++) {
		lcode[i] = (int *) calloc(gnum_op_conn, sizeof(int));
		for (j = 0; j < gnum_op_conn; j++) {
			lcode[i][j] = -1;
		}
	}

	F = (int *) calloc(gnum_ft_conn, sizeof(int));
	for (i = 0; i < gnum_ft_conn; i++) {
		F[i] = -1;
	}
	/* no-ops are included in the gop_conn!
	 */
	A = (int *) calloc(gnum_op_conn, sizeof(int));
	for (i = 0; i < gnum_op_conn; i++) {
		A[i] = -1;
	}

	/* layer 0
	 */
	for (i = 0; i < ginitial_state.num_F; i++) {
		F[ginitial_state.F[i]] = 0;
	}

	printf("\n\ncreating action-based encoding...");

	/* prec constraints, + code assignment.
	 */
	lnum_clauses = 0;
	code = 1; /* variables numbered 1 .. n */
	printf("\nbuilding rplan graph layers --> up to layer %d...", layer);
	for (t = 0; t < layer; t++) {
		for (i = 0; i < gnum_op_conn; i++) {
			/* Razer - buffer de acao i é -1 */
			if (A[i] == -1) {

				/* Razer - Para todas as pre-condicoes do operador i ... */
				for (j = 0; j < gop_conn[i].num_P; j++) {
					if (F[gop_conn[i].P[j]] == -1 || F[gop_conn[i].P[j]] > t)
						break;
				}
				if (j < gop_conn[i].num_P)
					continue;
				/* now i is an op that comes in here.
				 */
				/* Razer - O laco acima varreu F e os indices
				 sao ou -1 ou > t (layer)

				 Razer - buffer de acao i é t (o layer) */
				A[i] = t;
				if (0) {
					printf("\nA %d at %d", i, t);
				}
				/* mark its add effects.
				 */
				/* Razer - Para todos os efeitos (add) da operacao i
				 marca em F para o proximo layer */
				for (j = 0; j < gop_conn[i].num_A; j++) {
					ft = gop_conn[i].A[j];
					if (F[ft] != -1)
						continue;
					F[ft] = t + 1;
				}
			}

			/* Razer - neste ponto, o buffer A contem as
			 acoes disparadas neste layer e F contem os
			 fatos adicionados (proximo layer) */

			/* insert prec clauses, if at t > 0.
			 */
			/* Razer - se for o primeiro layer, nao tem
			 precondicao */
			if (t == 0) {
				continue;
			}

			/* Razer - vai setar as precondicoes
			 Para todas as precondicoes da acao i... */
			for (j = 0; j < gop_conn[i].num_P; j++) {
				/* Razer - obtem o fato que eh precondicao */
				ft = gop_conn[i].P[j];

				if (lnum_clauses == MAX_CLAUSES) {
					printf(
							"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}

				/* Razer - aloca uma clausula para esta precondicao
				 O tamanho da clausula eh o numero de operadores dos quais
				 este fato eh add */
				lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A + 1,
						sizeof(int));
				/* here the op i is used at t, for the 1st time. assign the code.
				 */
				if (j == 0) {
					if (lcode[t][i] != -1) {
						printf(
								"\n\nEXIT: op code %d at %d already assigned??\n\n",
								i, t);
						exit(1);
					}
					if (0) {
						printf("\nC %d at %d", i, t);
					}
					/* Razer - guarda em lcode [layer][operador] o valor code
					 code guarda numeracao sequencial de variaveis */
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					/* Razer - lop_to_code e ltime_to_code servem para
					 fazer referencia reversa com lcode
					 lop_to_code [ variavel ]  - retorna o operador
					 ltime_to_code [ variavel ] - retorna o layer */
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}

				/* Razer - Primeira variavel da clausula eh a acao i do layer t
				 Nega o operador (se nao for MHF)
				 OK colocar um if para gerar MHF */
				if (gcmd_line.makeMHF == 1)
					lclause[lnum_clauses][0] =  lcode[t][i];
				else
					lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				lclause_size[lnum_clauses] = 1;

				/* Razer - Para todas as operacoes para as quais
				 o fato ft eh add ... */
				for (k = 0; k < gft_conn[ft].num_A; k++) {

					/* Razer - retorna uma operacao para a qual o
					 fato ft eh add... */
					op = gft_conn[ft].A[k];
					if (A[op] == -1 || A[op] > t - 1) {
						continue;
					}
					/* Razer - Se no layer anterior esta
					 operacao nao esta marcada... */
					if (lcode[t - 1][op] == -1) {
						/* Razer - Marca a operacao */
						lcode[t - 1][op] = code++;
						if (0) {
							printf("\npC %d at %d", op, t - 1);
						}
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t - 1;
					}
					/* Razer - acrescenta a operacao as clausulas
					 OK adicionar um IF para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
								(-1) * lcode[t - 1][op];
					else
						lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
								lcode[t - 1][op];
				}
				if (lclause_size[lnum_clauses] == 1) {
					printf("\n\nEXIT: no achiever in at t>0??\n\n");
					exit(1);
				}
				nAclauses++;
				lnum_clauses++;
			} /* pres of i-op */
		} /* i -- op */
	} /* t */

	/* goal constraints
	 */
	printf("\ngoal constraints...");
	for (i = 0; i < ggoal_state.num_F; i++) {
		ft = ggoal_state.F[i];

		if (lnum_clauses == MAX_CLAUSES) {
			printf("\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
			exit(1);
		}
		lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A, sizeof(int));
		lclause_size[lnum_clauses] = 0;
		for (k = 0; k < gft_conn[ft].num_A; k++) {
			op = gft_conn[ft].A[k];
			if (A[op] == -1 || A[op] > layer - 1) {
				continue;
			}
			if (lcode[layer - 1][op] == -1) {
				lcode[layer - 1][op] = code++;
				if (code == MAX_CNF_VARS + 1) {
					printf(
							"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
					exit(1);
				}
				lop_to_code[code - 1] = op;
				ltime_to_code[code - 1] = layer - 1;
			}
			/* OK Colocar um IF aqui para gerar MHF */
			if (gcmd_line.makeMHF == 1)
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
						(-1) * lcode[layer - 1][op];
			else
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
						lcode[layer - 1][op];
		}
		if (lclause_size[lnum_clauses] == 0) {
			printf("\n\nno achiever in for goal?? deadline too low!\n\n");
			exit(UNSAT);
		}
		lnum_clauses++;
		nGclauses++;
	} /* goals */

	/* exclusion constraints. implementation a bit smart, to avoid
	 * time-consuming all-op-pairs-check.
	 */
	printf("\nbuilding exclusion constraints --> up to layer %d...", layer);
	for (t = 0; t < layer; t++) {
		for (i = 0; i < gnum_op_conn; i++) {
			if (A[i] == -1 || A[i] > t)
				continue;
			prevcl = lnum_clauses;
			for (j = 0; j < gop_conn[i].num_D; j++) {
				ft = gop_conn[i].D[j];
				for (k = 0; k < gft_conn[ft].num_P; k++) {
					op = gft_conn[ft].P[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh uma operacao
					 OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}

					/* OK colocar um IF aqui para gerar o MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] =  lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is pre of */
				for (k = 0; k < gft_conn[ft].num_A; k++) {
					op = gft_conn[ft].A[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is added by */
			} /* j: fts that i dels */

			for (j = 0; j < gop_conn[i].num_P; j++) {
				ft = gop_conn[i].P[j];
				for (k = 0; k < gft_conn[ft].num_D; k++) {
					op = gft_conn[ft].D[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh um operador
					 OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is del by */
			} /* j: fts that i has as prec */

			for (j = 0; j < gop_conn[i].num_A; j++) {
				ft = gop_conn[i].A[j];
				for (k = 0; k < gft_conn[ft].num_D; k++) {
					op = gft_conn[ft].D[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh um operador
					 OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];

					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is del by */
			} /* j: fts that i adds */
		} /* i: ops at t */
	} /* t */

	/* that's it. print CNF file.
	 */
	if (gcmd_line.debug) {
		if ((VARFILE = fopen(gcmd_line.varFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open VARFILE file.\n\n");
			exit(1);
		}
		fprintf(VARFILE, "\n\nc DECISION LAYER %d, ACTION-BASED ENCODING.",
				layer);
		fprintf(VARFILE, "\n\nc VARS:");

		for (i = 1; i < code; i++) {
			fprintf(VARFILE, "\nc var %2d action (", i);
			print_op_nameToFile(lop_to_code[i], VARFILE);
			fprintf(VARFILE, ") %d", ltime_to_code[i]);
		}
		/*
		 fprintf(VARFILE, "\n\nCLAUSES:");
		 for ( i = 0; i < lnum_clauses; i++ ) {
		 for ( j = 0; j < lclause_size[i]; j++ ) {
		 if ( lclause[i][j] > 0 ) {
		 fprintf(VARFILE, "\n%6d - ", i);
		 fprintf(VARFILE, "(");
		 print_op_nameToFile( lop_to_code[lclause[i][j]], VARFILE );
		 fprintf(VARFILE, " at %d) VAR = %d", ltime_to_code[lclause[i][j]], lclause[i][j] );
		 } else {
		 fprintf(VARFILE, "\n%6d - ", i);
		 fprintf(VARFILE, "(NOT ");
		 print_op_nameToFile( lop_to_code[(-1)*lclause[i][j]], VARFILE );
		 fprintf(VARFILE, " at %d) VAR = %d", ltime_to_code[(-1)*lclause[i][j]], lclause[i][j] );
		 }
		 }
		 }
		 fprintf(VARFILE, "0\n");
		 */
		fclose(VARFILE);
	}

	printf(
			"\n\nDECISION LAYER %d, WRITING ACTION-BASED ENCODING WITH %d VARS, %d CLAUSES.",
			layer, code - 1, lnum_clauses);
	printf("\n%d G clauses, %d A clauses, %d E clauses.", nGclauses, nAclauses,
			nEclauses);

	if (create == 0) {
		if ((CNF = fopen(gcmd_line.cnfFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open CNF file.\n\n");
			exit(1);
		}

		fprintf(CNF,
				"c CNF file planning task -p %s, -o %s, -f %s, bound %d, action based encoding\n",
				gcmd_line.path, gcmd_line.ops_file_name,
				gcmd_line.fct_file_name, layer);
		printf("\nb-check %d\n", gcmd_line.binary_clause_only);
		tmpNumber = lnum_clauses;
		if (gcmd_line.binary_clause_only != 0) {
			for (i = 0; i < tmpNumber; ++i) {
				if (lclause_size[i] > 2)
					--lnum_clauses;
			}
		}
		if (gcmd_line.makePBS == 1) {
				fprintf(CNF, "* #variable= %d #constraint= %d\n", code - 1, lnum_clauses);
				for (i = 0; i < tmpNumber; i++) {
						if (gcmd_line.binary_clause_only == 0 || lclause_size[i] < 3) {
								for (j = 0; j < lclause_size[i]; j++) {
										if (lclause[i][j] < 0)
												fprintf(CNF, "+1 ~x%d ", -1*lclause[i][j]);
										else
												fprintf(CNF, "+1 x%d ", lclause[i][j]);
								}
								fprintf(CNF, " >= 1;\n");
						}
				}
				fclose(CNF);
		}
		else {
	
			fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);
			for (i = 0; i < tmpNumber; i++) {
				if (gcmd_line.binary_clause_only == 0 || lclause_size[i] < 3) {
					for (j = 0; j < lclause_size[i]; j++) {
						fprintf(CNF, "%d ", lclause[i][j]);
					}
					fprintf(CNF, "0\n");
				}
			}
			fclose(CNF);
		}
		/* Razer - generate prefs */
		if (gcmd_line.makePREFS == 1) {
			/* the first variable or 2 CNF POSITIVE is generated as prefs.txt */
			FILE *prefs;

			char* vec_2cnf;
			vec_2cnf = (char*)malloc((MAX_CLAUSES) * sizeof(char));
			memset(vec_2cnf, 0, (MAX_CLAUSES));


			for (i = 0; i < tmpNumber; i++) {
				if (lclause_size[i] == 2) {
					/* binary - 2cnf - monotone - positive */
					for (j = 0; j < lclause_size[i]; j++) {
						int x = abs(lclause[i][j]);
						vec_2cnf[x] = 1;
					}
				}
			}


			if ((prefs = fopen("prefs.txt", "w")) == NULL ) {
				printf("\n\ncan't open PREFS file.\n\n");
				exit(1);
			}

			for (i=0; i<tmpNumber; i++) {
			   if (vec_2cnf[i]) {
			 		fprintf(prefs, "%d\n", i);
				}
			}
			fclose(prefs);
		}
	}
}

/* action-based
 */
void print_action_based_encoding(int layer, int create)

{
	FILE *CNF, *VARFILE;

	int i, j, t, k, ft, op, prevcl, l;
	int *F, *A;
	int code;
	int tmpNumber;

	int nGclauses = 0, nAclauses = 0, nEclauses = 0;

	lclause = (int **) calloc(MAX_CLAUSES, sizeof(int *));
	lclause_size = (int *) calloc(MAX_CLAUSES, sizeof(int));
	lcode = (int **) calloc(layer, sizeof(int *));
	lop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ltime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i < layer; i++) {
		lcode[i] = (int *) calloc(gnum_op_conn, sizeof(int));
		for (j = 0; j < gnum_op_conn; j++) {
			lcode[i][j] = -1;
		}
	}

	F = (int *) calloc(gnum_ft_conn, sizeof(int));
	for (i = 0; i < gnum_ft_conn; i++) {
		F[i] = -1;
	}
	/* no-ops are included in the gop_conn!
	 */
	A = (int *) calloc(gnum_op_conn, sizeof(int));
	for (i = 0; i < gnum_op_conn; i++) {
		A[i] = -1;
	}

	/* layer 0
	 */
	for (i = 0; i < ginitial_state.num_F; i++) {
		F[ginitial_state.F[i]] = 0;
	}

	printf("\n\ncreating action-based encoding...");

	/* prec constraints, + code assignment.
	 */
	lnum_clauses = 0;
	code = 1; /* variables numbered 1 .. n */
	printf("\nbuilding rplan graph layers --> up to layer %d...", layer);
	for (t = 0; t < layer; t++) {
		for (i = 0; i < gnum_op_conn; i++) {
			/* Razer - buffer de acao i é -1 */
			if (A[i] == -1) {

				/* Razer - Para todas as pre-condicoes do operador i ... */
				for (j = 0; j < gop_conn[i].num_P; j++) {
					if (F[gop_conn[i].P[j]] == -1 || F[gop_conn[i].P[j]] > t)
						break;
				}
				if (j < gop_conn[i].num_P)
					continue;
				/* now i is an op that comes in here.
				 */
				/* Razer - O laco acima varreu F e os indices
				 sao ou -1 ou > t (layer)

				 Razer - buffer de acao i é t (o layer) */
				A[i] = t;
				if (0) {
					printf("\nA %d at %d", i, t);
				}
				/* mark its add effects.
				 */
				/* Razer - Para todos os efeitos (add) da operacao i
				 marca em F para o proximo layer */
				for (j = 0; j < gop_conn[i].num_A; j++) {
					ft = gop_conn[i].A[j];
					if (F[ft] != -1)
						continue;
					F[ft] = t + 1;
				}
			}

			/* Razer - neste ponto, o buffer A contem as
			 acoes disparadas neste layer e F contem os
			 fatos adicionados (proximo layer) */

			/* insert prec clauses, if at t > 0.
			 */
			/* Razer - se for o primeiro layer, nao tem
			 precondicao */
			if (t == 0) {
				continue;
			}

			/* Razer - vai setar as precondicoes
			 Para todas as precondicoes da acao i... */
			for (j = 0; j < gop_conn[i].num_P; j++) {
				/* Razer - obtem o fato que eh precondicao */
				ft = gop_conn[i].P[j];

				if (lnum_clauses == MAX_CLAUSES) {
					printf(
							"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}

				/* Razer - aloca uma clausula para esta precondicao
				 O tamanho da clausula eh o numero de operadores dos quais
				 este fato eh add */
				lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A + 1,
						sizeof(int));
				/* here the op i is used at t, for the 1st time. assign the code.
				 */
				if (j == 0) {
					if (lcode[t][i] != -1) {
						printf(
								"\n\nEXIT: op code %d at %d already assigned??\n\n",
								i, t);
						exit(1);
					}
					if (0) {
						printf("\nC %d at %d", i, t);
					}
					/* Razer - guarda em lcode [layer][operador] o valor code
					 code guarda numeracao sequencial de variaveis */
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					/* Razer - lop_to_code e ltime_to_code servem para
					 fazer referencia reversa com lcode
					 lop_to_code [ variavel ]  - retorna o operador
					 ltime_to_code [ variavel ] - retorna o layer */
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}

				/* Razer - Primeira variavel da clausula eh a acao i do layer t
				 Nega o operador (se nao for MHF)
				 TODO OK colocar um if para gerar MHF */
				if (gcmd_line.makeMHF == 1)
					lclause[lnum_clauses][0] =  lcode[t][i];
				else
					lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				lclause_size[lnum_clauses] = 1;

				/* Razer - Para todas as operacoes para as quais
				 o fato ft eh add ... */
				for (k = 0; k < gft_conn[ft].num_A; k++) {

					/* Razer - retorna uma operacao para a qual o
					 fato ft eh add... */
					op = gft_conn[ft].A[k];
					if (A[op] == -1 || A[op] > t - 1) {
						continue;
					}
					/* Razer - Se no layer anterior esta
					 operacao nao esta marcada... */
					if (lcode[t - 1][op] == -1) {
						/* Razer - Marca a operacao */
						lcode[t - 1][op] = code++;
						if (0) {
							printf("\npC %d at %d", op, t - 1);
						}
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t - 1;
					}
					/* Razer - acrescenta a operacao as clausulas
					 TODO OK adicionar um IF para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
								(-1) * lcode[t - 1][op];
					else
						lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
								lcode[t - 1][op];
				}
				if (lclause_size[lnum_clauses] == 1) {
					printf("\n\nEXIT: no achiever in at t>0??\n\n");
					exit(1);
				}
				nAclauses++;
				lnum_clauses++;
			} /* pres of i-op */
		} /* i -- op */
	} /* t */

	/* goal constraints
	 */
	printf("\ngoal constraints...");
	for (i = 0; i < ggoal_state.num_F; i++) {
		ft = ggoal_state.F[i];

		if (lnum_clauses == MAX_CLAUSES) {
			printf("\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
			exit(1);
		}
		lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A, sizeof(int));
		lclause_size[lnum_clauses] = 0;
		for (k = 0; k < gft_conn[ft].num_A; k++) {
			op = gft_conn[ft].A[k];
			if (A[op] == -1 || A[op] > layer - 1) {
				continue;
			}
			if (lcode[layer - 1][op] == -1) {
				lcode[layer - 1][op] = code++;
				if (code == MAX_CNF_VARS + 1) {
					printf(
							"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
					exit(1);
				}
				lop_to_code[code - 1] = op;
				ltime_to_code[code - 1] = layer - 1;
			}
			/* TODO OK Colocar um IF aqui para gerar MHF */
			if (gcmd_line.makeMHF == 1)
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
						(-1) * lcode[layer - 1][op];
			else
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
						lcode[layer - 1][op];
		}
		if (lclause_size[lnum_clauses] == 0) {
			printf("\n\nno achiever in for goal?? deadline too low!\n\n");
			exit(UNSAT);
		}
		lnum_clauses++;
		nGclauses++;
	} /* goals */

	/* exclusion constraints. implementation a bit smart, to avoid
	 * time-consuming all-op-pairs-check.
	 */
	printf("\nbuilding exclusion constraints --> up to layer %d...", layer);
	for (t = 0; t < layer; t++) {
		for (i = 0; i < gnum_op_conn; i++) {
			if (A[i] == -1 || A[i] > t)
				continue;
			prevcl = lnum_clauses;
			for (j = 0; j < gop_conn[i].num_D; j++) {
				ft = gop_conn[i].D[j];
				for (k = 0; k < gft_conn[ft].num_P; k++) {
					op = gft_conn[ft].P[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh uma operacao
					 TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}

					/* TODO OK colocar um IF aqui para gerar o MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] =  lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is pre of */
				for (k = 0; k < gft_conn[ft].num_A; k++) {
					op = gft_conn[ft].A[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is added by */
			} /* j: fts that i dels */

			for (j = 0; j < gop_conn[i].num_P; j++) {
				ft = gop_conn[i].P[j];
				for (k = 0; k < gft_conn[ft].num_D; k++) {
					op = gft_conn[ft].D[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh um operador
					 TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];
					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is del by */
			} /* j: fts that i has as prec */

			for (j = 0; j < gop_conn[i].num_A; j++) {
				ft = gop_conn[i].A[j];
				for (k = 0; k < gft_conn[ft].num_D; k++) {
					op = gft_conn[ft].D[k];
					if (op <= i)
						continue; /* only in one of the two dirs we'll get */
					if (A[op] == -1 || A[op] > t)
						continue;
					/* did we make op excl of i already?
					 */
					if (lcode[t][op] != -1) {
						for (l = prevcl; l < lnum_clauses; l++) {
							if (lclause[l][1] == (-1) * lcode[t][op])
								break;
						}
						if (l < lnum_clauses)
							continue; /* yes. */
					}
					/* record the clause.
					 */
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\nEXIT: too many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
					if (lcode[t][i] == -1) {
						lcode[t][i] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = i;
						ltime_to_code[code - 1] = t;
					}
					/* Razer - i eh um operador
					 TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][0] = lcode[t][i];
					else
						lclause[lnum_clauses][0] = (-1) * lcode[t][i];
					if (lcode[t][op] == -1) {
						lcode[t][op] = code++;
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\nEXIT: too many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t;
					}
					/* TODO OK Colocar um IF aqui para gerar MHF */
					if (gcmd_line.makeMHF == 1)
						lclause[lnum_clauses][1] = lcode[t][op];
					else
						lclause[lnum_clauses][1] = (-1) * lcode[t][op];

					lclause_size[lnum_clauses] = 2;
					lnum_clauses++;
					nEclauses++;
				} /* k: ops that ft is del by */
			} /* j: fts that i adds */
		} /* i: ops at t */
	} /* t */

	/* that's it. print CNF file.
	 */
	if (gcmd_line.debug) {
		if ((VARFILE = fopen(gcmd_line.varFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open VARFILE file.\n\n");
			exit(1);
		}
		fprintf(VARFILE, "\n\nc DECISION LAYER %d, ACTION-BASED ENCODING.",
				layer);
		fprintf(VARFILE, "\n\nc VARS:");

		for (i = 1; i < code; i++) {
			fprintf(VARFILE, "\nc var %2d action (", i);
			print_op_nameToFile(lop_to_code[i], VARFILE);
			fprintf(VARFILE, ") %d", ltime_to_code[i]);
		}
		/*
		 fprintf(VARFILE, "\n\nCLAUSES:");
		 for ( i = 0; i < lnum_clauses; i++ ) {
		 for ( j = 0; j < lclause_size[i]; j++ ) {
		 if ( lclause[i][j] > 0 ) {
		 fprintf(VARFILE, "\n%6d - ", i);
		 fprintf(VARFILE, "(");
		 print_op_nameToFile( lop_to_code[lclause[i][j]], VARFILE );
		 fprintf(VARFILE, " at %d) VAR = %d", ltime_to_code[lclause[i][j]], lclause[i][j] );
		 } else {
		 fprintf(VARFILE, "\n%6d - ", i);
		 fprintf(VARFILE, "(NOT ");
		 print_op_nameToFile( lop_to_code[(-1)*lclause[i][j]], VARFILE );
		 fprintf(VARFILE, " at %d) VAR = %d", ltime_to_code[(-1)*lclause[i][j]], lclause[i][j] );
		 }
		 }
		 }
		 fprintf(VARFILE, "0\n");
		 */
		fclose(VARFILE);
	}

	printf(
			"\n\nDECISION LAYER %d, WRITING ACTION-BASED ENCODING WITH %d VARS, %d CLAUSES.",
			layer, code - 1, lnum_clauses);
	printf("\n%d G clauses, %d A clauses, %d E clauses.", nGclauses, nAclauses,
			nEclauses);

	if (create == 0) {
		if ((CNF = fopen(gcmd_line.cnfFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open CNF file.\n\n");
			exit(1);
		}

		fprintf(CNF,
				"c CNF file planning task -p %s, -o %s, -f %s, bound %d, action based encoding\n",
				gcmd_line.path, gcmd_line.ops_file_name,
				gcmd_line.fct_file_name, layer);
		printf("\nb-check %d\n", gcmd_line.binary_clause_only);
		tmpNumber = lnum_clauses;
		if (gcmd_line.binary_clause_only != 0) {
			for (i = 0; i < tmpNumber; ++i) {
				if (lclause_size[i] > 2)
					--lnum_clauses;
			}
		}
		fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);
		for (i = 0; i < tmpNumber; i++) {
			if (gcmd_line.binary_clause_only == 0 || lclause_size[i] < 3) {
				for (j = 0; j < lclause_size[i]; j++) {
					fprintf(CNF, "%d ", lclause[i][j]);
				}
				fprintf(CNF, "0\n");
			}
		}
		fclose(CNF);
	}
}


/* gp-style action-based
 */

void print_gpstyle_action_based_encoding(int layer, int create) {

	FILE *VARFILE, *CNF;

	int i, j, t, ft, k, op, code;
	IntList *tmp, *i1, *i2;

	lclause = (int **) calloc(MAX_CLAUSES, sizeof(int *));
	lclause_size = (int *) calloc(MAX_CLAUSES, sizeof(int));
	lcode = (int **) calloc(layer, sizeof(int *));
	lop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ltime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i < layer; i++) {
		lcode[i] = (int *) calloc(gnum_op_conn, sizeof(int));
		for (j = 0; j < gnum_op_conn; j++) {
			lcode[i][j] = -1;
		}
	}

	/* build the graph up to <layer>
	 */
	for (i = 0; i < gnum_op_conn; i++) {
		tmp = new_IntList(i);
		if (gout_ops) {
			gout_ops->prev = tmp;
		}
		tmp->next = gout_ops;
		gout_ops = tmp;
	}
	for (i = 0; i < ginitial_state.num_F; i++) {
		ft = ginitial_state.F[i];
		gin_ft_count++;
		gft_conn[ft].first_appearance = 0;
		gft_conn[ft].info_at[0] = new_FtLevelInfo();
		tmp = new_IntList(ft);
		tmp->next = gin_fts;
		gin_fts = tmp;
	}
	gin_fts_at[0] = gin_fts;
	if (gcmd_line.display_info) {
		printf("\ntime: %3d, %5d facts and %7d exclusive pairs", 0,
				gin_ft_count, gin_ft_exclusion_count);
		fflush(stdout);
	}
	for (t = 0; t < layer; t++) {
		build_graph_evolution_step();
	}

	printf("\n\ncreating gp-style action-based encoding...");

	/* prec constraints, + code assignment.
	 */
	lnum_clauses = 0;
	code = 1; /* variables numbered 1 .. n */
	for (t = 0; t < layer; t++) {
		printf("\nplan graph layer %d...", t);
		for (i = 0; i < gnum_op_conn; i++) {
			if (gop_conn[i].info_at[t] == NULL /* equiv to not in here */) {
				continue;
			}
			/* insert prec clauses, if at t > 0.
			 */
			if (t == 0) {
				continue;
			}
			for (j = 0; j < gop_conn[i].num_P; j++) {
				ft = gop_conn[i].P[j];

				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A + 1,
						sizeof(int));
				/* here the op i is used at t, for the 1st time. assign the code.
				 */
				if (j == 0) {
					if (lcode[t][i] != -1) {
						printf("\n\nop code %d at %d already assigned??\n\n", i,
								t);
						exit(UNSAT);
					}
					if (0) {
						printf("\nC %d at %d", i, t);
					}
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}

				lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				lclause_size[lnum_clauses] = 1;
				for (k = 0; k < gft_conn[ft].num_A; k++) {
					op = gft_conn[ft].A[k];
					if (gop_conn[op].info_at[t - 1] == NULL ) {
						continue;
					}
					if (lcode[t - 1][op] == -1) {
						lcode[t - 1][op] = code++;
						if (0) {
							printf("\npC %d at %d", op, t - 1);
						}
						if (code == MAX_CNF_VARS + 1) {
							printf(
									"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
							exit(1);
						}
						lop_to_code[code - 1] = op;
						ltime_to_code[code - 1] = t - 1;
					}
					lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
							lcode[t - 1][op];
				}
				if (lclause_size[lnum_clauses] == 1) {
					printf("\n\nno achiever in at t>0??\n\n");
					exit(UNSAT);
				}
				lnum_clauses++;
			} /* pres of i-op */
		} /* i -- op */
	} /* t */

	/* goal constraints
	 */
	printf("\ngoal constraints...");
	for (i = 0; i < ggoal_state.num_F; i++) {
		ft = ggoal_state.F[i];

		if (lnum_clauses == MAX_CLAUSES) {
			printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
			exit(1);
		}
		lclause[lnum_clauses] = (int *) calloc(gft_conn[ft].num_A, sizeof(int));
		lclause_size[lnum_clauses] = 0;
		for (k = 0; k < gft_conn[ft].num_A; k++) {
			op = gft_conn[ft].A[k];
			if (gop_conn[op].info_at[layer - 1] == NULL ) {
				continue;
			}
			if (lcode[layer - 1][op] == -1) {
				lcode[layer - 1][op] = code++;
				if (code == MAX_CNF_VARS + 1) {
					printf("\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
					exit(1);
				}
				lop_to_code[code - 1] = op;
				ltime_to_code[code - 1] = layer - 1;
			}
			lclause[lnum_clauses][lclause_size[lnum_clauses]++] = lcode[layer
					- 1][op];
		}
		if (lclause_size[lnum_clauses] == 0) {
			printf("\n\nno achiever in for goal?? deadline too low!\n\n");
			exit(UNSAT);
		}
		lnum_clauses++;
	} /* goals */

	/* exclusion constraints.
	 */
	for (t = 0; t < layer; t++) {
		printf("\nexclusion constraints layer %d...", t);
		for (i1 = gin_ops_at[t]; i1 && i1->next; i1 = i1->next) {
			i = i1->i1;
			for (i2 = i1->next; i2; i2 = i2->next) {
				j = i2->i1;
				if (!(gop_conn[i].info_at[t]->bit_exclusives[gop_conn[j].uid_block]
						& gop_conn[j].uid_mask)) {
					continue;
				}
				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
				if (lcode[t][i] == -1) {
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				if (lcode[t][j] == -1) {
					lcode[t][j] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = j;
					ltime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][1] = (-1) * lcode[t][j];
				lclause_size[lnum_clauses] = 2;
				lnum_clauses++;
			}
		}
	}

	/* that's it; print CNF file. */
	/*Start Timer*/
	clock_t start, end;
	double execution_time;
	start = clock();

	if (gcmd_line.debug) {
		/* debugging: print semantic version of clause set.
		 */

		if ((VARFILE = fopen(gcmd_line.varFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open VARFILE file.\n\n");
			exit(1);
		}
		fprintf(VARFILE,
				"\n\nc DECISION LAYER %d, GP-STYLE ACTION-BASED ENCODING.",
				layer);
		fprintf(VARFILE, "\n\nc VARS:");

		for (i = 1; i < code; i++) {
			fprintf(VARFILE, "\nc var %6d action (", i);
			print_op_nameToFile(lop_to_code[i], VARFILE);
			fprintf(VARFILE, ") %d", ltime_to_code[i]);
		}

		fclose(VARFILE);
	}

	printf(
			"\n\nDECISION LAYER %d, WRITING GP-STYLE ACTION-BASED ENCODING WITH %d VARS, %d CLAUSES.",
			layer, code - 1, lnum_clauses);

	if (create == 0) {
		if ((CNF = fopen(gcmd_line.cnfFileName, "w")) == NULL ) {
			printf("\n\ncan't open CNF file.\n\n");
			exit(1);
		}

		fprintf(CNF,
				"c CNF file planning task -p %s, -o %s, -f %s, bound %d, gp-style action-based encoding\n",
				gcmd_line.path, gcmd_line.ops_file_name,
				gcmd_line.fct_file_name, layer);

		fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);
		for (i = 0; i < lnum_clauses; i++) {
			for (j = 0; j < lclause_size[i]; j++) {
				fprintf(CNF, "%d ", lclause[i][j]);
			}
			fprintf(CNF, "0\n");
		}
		fclose(CNF);
	}
	/* end timer */
	end = clock();
	execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
	printf("\n=======NEW=============================================\n");
	printf("Exectuion time: %fs", execution_time);
	printf("\n=======================================================\n");
}

/* gp-based
 */

void print_gp_based_encoding(int layer, int create)

{

	FILE *VARFILE, *CNF;

	int i, j, t, ft, op, code;
	IntList *tmp, *i1, *i2;

	/* have to separate the ft coding out from the op coding.
	 */
	int **fcode;
	int *fop_to_code;
	int *ftime_to_code;

	lclause = (int **) calloc(MAX_CLAUSES, sizeof(int *));
	lclause_size = (int *) calloc(MAX_CLAUSES, sizeof(int));
	lcode = (int **) calloc(layer, sizeof(int *));
	lop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ltime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i < layer; i++) {
		lcode[i] = (int *) calloc(gnum_op_conn, sizeof(int));
		for (j = 0; j < gnum_op_conn; j++) {
			lcode[i][j] = -1;
		}
	}
	fcode = (int **) calloc(layer + 1, sizeof(int *));
	fop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ftime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i <= layer; i++) {
		fcode[i] = (int *) calloc(gnum_ft_conn, sizeof(int));
		for (j = 0; j < gnum_ft_conn; j++) {
			fcode[i][j] = -1;
		}
	}

	/* build the graph up to <layer>
	 */
	for (i = 0; i < gnum_op_conn; i++) {
		tmp = new_IntList(i);
		if (gout_ops) {
			gout_ops->prev = tmp;
		}
		tmp->next = gout_ops;
		gout_ops = tmp;
	}
	for (i = 0; i < ginitial_state.num_F; i++) {
		ft = ginitial_state.F[i];
		gin_ft_count++;
		gft_conn[ft].first_appearance = 0;
		gft_conn[ft].info_at[0] = new_FtLevelInfo();
		tmp = new_IntList(ft);
		tmp->next = gin_fts;
		gin_fts = tmp;
	}
	gin_fts_at[0] = gin_fts;
	if (gcmd_line.display_info) {
		printf("\ntime: %3d, %5d facts and %7d exclusive pairs", 0,
				gin_ft_count, gin_ft_exclusion_count);
		fflush(stdout);
	}
	for (t = 0; t < layer; t++) {
		build_graph_evolution_step();
		fflush(stdout);
	}

	printf("\n\ncreating gp-based encoding...");

	/* prec constraints, + code assignment.
	 */
	lnum_clauses = 0;
	code = 1; /* variables numbered 1 .. n */
	for (t = 0; t <= layer; t++) {
		printf("\nplan graph layer %d...", t);
		for (i = 0; i < gnum_ft_conn; i++) {
			if (gft_conn[i].info_at[t] == NULL /* equiv to not in here */) {
				continue;
			}
			/* insert adder clause, if at t > 0. else, say it has to be true,
			 * if it's an initial fact.
			 */
			if (t == 0) {
				for (j = 0; j < ginitial_state.num_F; j++) {
					if (ginitial_state.F[j] == i)
						break;
				}
				if (j < ginitial_state.num_F) {
					fcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					fop_to_code[code - 1] = i;
					ftime_to_code[code - 1] = t;
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
					lclause[lnum_clauses][0] = fcode[t][i];
					lclause_size[lnum_clauses] = 1;
				}
				continue;
			}
			if (fcode[t][i] != -1) {
				printf("\n\nft already coded??\n\n");
				exit(UNSAT);
			}
			fcode[t][i] = code++;
			if (code == MAX_CNF_VARS + 1) {
				printf("\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
				exit(1);
			}
			fop_to_code[code - 1] = i;
			ftime_to_code[code - 1] = t;
			if (lnum_clauses == MAX_CLAUSES) {
				printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
				exit(1);
			}
			lclause[lnum_clauses] = (int *) calloc(gft_conn[i].num_A + 1,
					sizeof(int));
			lclause[lnum_clauses][0] = (-1) * fcode[t][i];
			lclause_size[lnum_clauses] = 1;
			for (j = 0; j < gft_conn[i].num_A; j++) {
				op = gft_conn[i].A[j];
				if (gop_conn[op].info_at[t - 1] == NULL ) {
					continue;
				}
				if (lcode[t - 1][op] == -1) {
					lcode[t - 1][op] = code++;
					if (0) {
						printf("\npC %d at %d", op, t - 1);
					}
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = op;
					ltime_to_code[code - 1] = t - 1;
				}
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] = lcode[t
						- 1][op];
			}
			if (lclause_size[lnum_clauses] == 1) {
				printf("\n\nno achiever in at t>0??\n\n");
				exit(UNSAT);
			}
			lnum_clauses++;
		} /* i-ft */

		if (t == layer) {
			continue;
		}

		for (i = 0; i < gnum_op_conn; i++) {
			if (gop_conn[i].info_at[t] == NULL /* equiv to not in here */) {
				continue;
			}
			/* insert prec clauses.
			 */
			for (j = 0; j < gop_conn[i].num_P; j++) {
				ft = gop_conn[i].P[j];

				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
				/* here the op i is used at t, for the 1st time. assign the code.
				 */
				if (j == 0) {
					if (lcode[t][i] != -1) {
						printf("\n\nop code %d at %d already assigned??\n\n", i,
								t);
						exit(UNSAT);
					}
					if (0) {
						printf("\nC %d at %d", i, t);
					}
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}

				lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				if (fcode[t][ft] == -1) {
					printf("\n\nprec fact not coded??\n\n");
					exit(1);
				}
				lclause[lnum_clauses][1] = fcode[t][ft];
				lclause_size[lnum_clauses] = 2;
				lnum_clauses++;
			} /* j: pres of i-op */
		} /* i -- op */
	} /* t */

	/* goal constraints
	 */
	printf("\ngoal constraints...");
	for (i = 0; i < ggoal_state.num_F; i++) {
		ft = ggoal_state.F[i];

		if (lnum_clauses == MAX_CLAUSES) {
			printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
			exit(1);
		}
		lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
		if (fcode[layer][ft] == -1) {
			printf("\n\ngoal fact not coded - level too low??\n\n");
			exit(UNSAT);
		}
		lclause[lnum_clauses][0] = fcode[layer][ft];
		lclause_size[lnum_clauses] = 1;
		lnum_clauses++;
	} /* goals */

	/* exclusion constraints.
	 */
	for (t = 0; t <= layer; t++) {
		printf("\nexclusion constraints layer %d...", t);
		for (i1 = gin_fts_at[t]; i1 && i1->next; i1 = i1->next) {
			i = i1->i1;
			for (i2 = i1->next; i2; i2 = i2->next) {
				j = i2->i1;
				if (!(gft_conn[i].info_at[t]->bit_exclusives[gft_conn[j].uid_block]
						& gft_conn[j].uid_mask)) {
					continue;
				}
				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
				if (fcode[t][i] == -1) {
					fcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					fop_to_code[code - 1] = i;
					ftime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][0] = (-1) * fcode[t][i];
				if (fcode[t][j] == -1) {
					fcode[t][j] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					fop_to_code[code - 1] = j;
					ftime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][1] = (-1) * fcode[t][j];
				lclause_size[lnum_clauses] = 2;
				lnum_clauses++;
			} /* i2 */
		} /* i1 */

		if (t == layer)
			continue;

		for (i1 = gin_ops_at[t]; i1 && i1->next; i1 = i1->next) {
			i = i1->i1;
			for (i2 = i1->next; i2; i2 = i2->next) {
				j = i2->i1;
				if (!(gop_conn[i].info_at[t]->bit_exclusives[gop_conn[j].uid_block]
						& gop_conn[j].uid_mask)) {
					continue;
				}
				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
				if (lcode[t][i] == -1) {
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				if (lcode[t][j] == -1) {
					lcode[t][j] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = j;
					ltime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][1] = (-1) * lcode[t][j];
				lclause_size[lnum_clauses] = 2;
				lnum_clauses++;
			}
		}
	}

	/* that's it. print CNF file.
	 */
	if (gcmd_line.debug) {
		/* debugging: print semantic version of clause set.
		 */

		if ((VARFILE = fopen(gcmd_line.varFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open VARFILE file.\n\n");
			exit(1);
		}
		fprintf(VARFILE, "\n\nc DECISION LAYER %d, GP-BASED ENCODING.", layer);
		fprintf(VARFILE, "\n\nc VARS:");

		for (i = 1; i < code; i++) {
			fprintf(VARFILE, "\nc var %6d action (", i);
			print_op_nameToFile(lop_to_code[i], VARFILE);
			fprintf(VARFILE, ") %d", ltime_to_code[i]);
		}

		fclose(VARFILE);
	}

	printf(
			"\n\nDECISION LAYER %d, WRITING GP-BASED ENCODING WITH %d VARS, %d CLAUSES.",
			layer, code - 1, lnum_clauses);

	if (create == 0) {
		if ((CNF = fopen(gcmd_line.cnfFileName, "w")) == NULL ) {
			printf("\n\ncan't open CNF file.\n\n");
			exit(1);
		}

		fprintf(CNF,
				"c CNF file planning task -p %s, -o %s, -f %s, bound %d, gp-based encoding\n",
				gcmd_line.path, gcmd_line.ops_file_name,
				gcmd_line.fct_file_name, layer);

		fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);
		for (i = 0; i < lnum_clauses; i++) {
			for (j = 0; j < lclause_size[i]; j++) {
				fprintf(CNF, "%d ", lclause[i][j]);
			}
			fprintf(CNF, "0\n");
		}
		fclose(CNF);
	}
}

/* thin gp-based
 */

void older_print_thin_gp_based_encoding(int layer, int create)

{
	FILE *CNF, *VARFILE;

	int i, j, t, ft, op, code;
	IntList *tmp, *i1, *i2;

	/* have to separate the ft coding out from the op coding.
	 */
	int **fcode;
	int *fop_to_code;
	int *ftime_to_code;

	lclause = (int **) calloc(MAX_CLAUSES, sizeof(int *));
	lclause_size = (int *) calloc(MAX_CLAUSES, sizeof(int));
	lcode = (int **) calloc(layer, sizeof(int *));
	lop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ltime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i < layer; i++) {
		lcode[i] = (int *) calloc(gnum_op_conn, sizeof(int));
		for (j = 0; j < gnum_op_conn; j++) {
			lcode[i][j] = -1;
		}
	}
	fcode = (int **) calloc(layer + 1, sizeof(int *));
	fop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ftime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i <= layer; i++) {
		fcode[i] = (int *) calloc(gnum_ft_conn, sizeof(int));
		for (j = 0; j < gnum_ft_conn; j++) {
			fcode[i][j] = -1;
		}
	}

	/* build the graph up to <layer>
	 */
	for (i = 0; i < gnum_op_conn; i++) {
		tmp = new_IntList(i);
		if (gout_ops) {
			gout_ops->prev = tmp;
		}
		tmp->next = gout_ops;
		gout_ops = tmp;
	}
	for (i = 0; i < ginitial_state.num_F; i++) {
		ft = ginitial_state.F[i];
		gin_ft_count++;
		gft_conn[ft].first_appearance = 0;
		gft_conn[ft].info_at[0] = new_FtLevelInfo();
		tmp = new_IntList(ft);
		tmp->next = gin_fts;
		gin_fts = tmp;
	}
	gin_fts_at[0] = gin_fts;
	if (gcmd_line.display_info) {
		printf("\ntime: %3d, %5d facts and %7d exclusive pairs", 0,
				gin_ft_count, gin_ft_exclusion_count);
		fflush(stdout);
	}
	for (t = 0; t < layer; t++) {
		build_graph_evolution_step();
	}

	printf("\n\ncreating thin gp-based encoding...");

	/* prec constraints, + code assignment.
	 */
	lnum_clauses = 0;
	code = 1; /* variables numbered 1 .. n */
	for (t = 0; t <= layer; t++) {
		printf("\nplan graph layer %d...", t);
		for (i = 0; i < gnum_ft_conn; i++) {
			if (gft_conn[i].info_at[t] == NULL /* equiv to not in here */) {
				continue;
			}
			/* insert adder clause, if at t > 0. else, say it has to be true,
			 * if it's an initial fact.
			 */
			if (t == 0) {
				for (j = 0; j < ginitial_state.num_F; j++) {
					if (ginitial_state.F[j] == i)
						break;
				}
				if (j < ginitial_state.num_F) {
					fcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					fop_to_code[code - 1] = i;
					ftime_to_code[code - 1] = t;
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
					lclause[lnum_clauses][0] = fcode[t][i];
					lclause_size[lnum_clauses] = 1;
				}
				continue;
			}
			if (fcode[t][i] != -1) {
				printf("\n\nft already coded??\n\n");
				exit(UNSAT);
			}
			fcode[t][i] = code++;
			if (code == MAX_CNF_VARS + 1) {
				printf("\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
				exit(1);
			}
			fop_to_code[code - 1] = i;
			ftime_to_code[code - 1] = t;
			if (lnum_clauses == MAX_CLAUSES) {
				printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
				exit(1);
			}
			lclause[lnum_clauses] = (int *) calloc(gft_conn[i].num_A + 1,
					sizeof(int));
			lclause[lnum_clauses][0] = (-1) * fcode[t][i];
			lclause_size[lnum_clauses] = 1;
			for (j = 0; j < gft_conn[i].num_A; j++) {
				op = gft_conn[i].A[j];
				if (gop_conn[op].info_at[t - 1] == NULL ) {
					continue;
				}
				if (lcode[t - 1][op] == -1) {
					lcode[t - 1][op] = code++;
					if (0) {
						printf("\npC %d at %d", op, t - 1);
					}
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = op;
					ltime_to_code[code - 1] = t - 1;
				}
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] = lcode[t
						- 1][op];
			}
			if (lclause_size[lnum_clauses] == 1) {
				printf("\n\nno achiever in at t>0??\n\n");
				exit(UNSAT);
			}
			lnum_clauses++;
		} /* i-ft */

		if (t == layer) {
			continue;
		}

		for (i = 0; i < gnum_op_conn; i++) {
			if (gop_conn[i].info_at[t] == NULL /* equiv to not in here */) {
				continue;
			}
			/* insert prec clauses.
			 */
			for (j = 0; j < gop_conn[i].num_P; j++) {
				ft = gop_conn[i].P[j];

				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
				/* here the op i is used at t, for the 1st time. assign the code.
				 */
				if (j == 0) {
					if (lcode[t][i] != -1) {
						printf("\n\nop code %d at %d already assigned??\n\n", i,
								t);
						exit(UNSAT);
					}
					if (0) {
						printf("\nC %d at %d", i, t);
					}
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}

				lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				if (fcode[t][ft] == -1) {
					printf("\n\nprec fact not coded??\n\n");
					exit(1);
				}
				lclause[lnum_clauses][1] = fcode[t][ft];
				lclause_size[lnum_clauses] = 2;
				lnum_clauses++;
			} /* j: pres of i-op */
		} /* i -- op */
	} /* t */

	/* goal constraints
	 */
	printf("\ngoal constraints...");
	for (i = 0; i < ggoal_state.num_F; i++) {
		ft = ggoal_state.F[i];

		if (lnum_clauses == MAX_CLAUSES) {
			printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
			exit(1);
		}
		lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
		if (fcode[layer][ft] == -1) {
			printf("\n\ngoal fact not coded - level too low??\n\n");
			exit(UNSAT);
		}
		lclause[lnum_clauses][0] = fcode[layer][ft];
		lclause_size[lnum_clauses] = 1;
		lnum_clauses++;
	} /* goals */

	/* exclusion constraints.
	 */
	for (t = 0; t < layer; t++) {
		printf("\nexclusion constraints layer %d...", t);

		for (i1 = gin_ops_at[t]; i1 && i1->next; i1 = i1->next) {
			i = i1->i1;
			for (i2 = i1->next; i2; i2 = i2->next) {
				j = i2->i1;
				if (!interfere(i, j)) {
					continue;
				}
				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
				if (lcode[t][i] == -1) {
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][0] = (-1) * lcode[t][i];
				if (lcode[t][j] == -1) {
					lcode[t][j] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = j;
					ltime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][1] = (-1) * lcode[t][j];
				lclause_size[lnum_clauses] = 2;
				lnum_clauses++;
			}
		}
	}

	/* that's it. print CNF file.
	 */
	if (gcmd_line.debug) {
		/* debugging: print semantic version of clause set.
		 */

		if ((VARFILE = fopen(gcmd_line.varFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open VARFILE file.\n\n");
			exit(1);
		}
		fprintf(VARFILE, "\n\nc DECISION LAYER %d, THIN GP-BASED ENCODING.",
				layer);
		fprintf(VARFILE, "\n\nc VARS:");

		for (i = 1; i < code; i++) {
			fprintf(VARFILE, "\nc var %2d action (", i);
			print_op_nameToFile(lop_to_code[i], VARFILE);
			fprintf(VARFILE, ") %d", ltime_to_code[i]);
		}

		/*
		 printf("\n\nCLAUSES:");
		 for ( i = 0; i < lnum_clauses; i++ ) {
		 printf("\n%6d - ", i);
		 if ( 1 ) {
		 for ( j = 0; j < lclause_size[i]; j++ ) {
		 printf("(%d)", lclause[i][j]);
		 if ( j < lclause_size[i]-1 ) printf(", ");
		 }
		 fflush(stdout);
		 }
		 for ( j = 0; j < lclause_size[i]; j++ ) {
		 if ( lclause[i][j] > 0 ) {
		 printf("(");
		 print_op_name( lop_to_code[lclause[i][j]] );
		 printf(" at %d)", ltime_to_code[lclause[i][j]] );
		 } else {
		 printf("(NOT ");
		 print_op_name( lop_to_code[(-1)*lclause[i][j]] );
		 printf(" at %d)", ltime_to_code[(-1)*lclause[i][j]] );
		 }
		 if ( j < lclause_size[i]-1 ) printf(", ");
		 }
		 }
		 */
		fclose(VARFILE);
	}

	printf(
			"\n\nDECISION LAYER %d, WRITING THIN GP-BASED ENCODING WITH %d VARS, %d CLAUSES.",
			layer, code - 1, lnum_clauses);

	if (create == 0) {
		if ((CNF = fopen(gcmd_line.cnfFileName, "w")) == NULL ) {
			printf("\n\ncan't open CNF file.\n\n");
			exit(1);
		}

		fprintf(CNF,
				"c CNF file planning task -p %s, -o %s, -f %s, bound %d, thin gp-based encoding\n",
				gcmd_line.path, gcmd_line.ops_file_name,
				gcmd_line.fct_file_name, layer);

		fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);
		for (i = 0; i < lnum_clauses; i++) {
			for (j = 0; j < lclause_size[i]; j++) {
				fprintf(CNF, "%d ", lclause[i][j]);
			}
			fprintf(CNF, "0\n");
		}
		fclose(CNF);
	}
}

void print_thin_gp_based_encoding(int layer, int create)

{
	FILE *CNF, *VARFILE;

	int i, j, t, ft, op, code;
	IntList *tmp, *i1, *i2;

	/* have to separate the ft coding out from the op coding.
	 */
	int **fcode;
	int *fop_to_code;
	int *ftime_to_code;


	/* Razer, para gerar MHF com pure literals */
	int cont_2cnf = 0;
	int cont_horn = 0;
	int cont_unit = 0;
	char* vec_2cnf;
	char* vec_horn;
	char* vec_unit;


		vec_2cnf = (char*)malloc((MAX_CLAUSES) * sizeof(char));
		vec_horn = (char*)malloc((MAX_CLAUSES) * sizeof(char));
		vec_unit = (char*)malloc((MAX_CLAUSES) * sizeof(char));

		memset(vec_2cnf, 0, (MAX_CLAUSES));
		memset(vec_horn, 0, (MAX_CLAUSES));
		memset(vec_unit, 0, (MAX_CLAUSES));


	lclause = (int **) calloc(MAX_CLAUSES, sizeof(int *));
	lclause_size = (int *) calloc(MAX_CLAUSES, sizeof(int));
	lcode = (int **) calloc(layer, sizeof(int *));
	lop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ltime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i < layer; i++) {
		lcode[i] = (int *) calloc(gnum_op_conn, sizeof(int));
		for (j = 0; j < gnum_op_conn; j++) {
			lcode[i][j] = -1;
		}
	}
	fcode = (int **) calloc(layer + 1, sizeof(int *));
	fop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	ftime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
	for (i = 0; i <= layer; i++) {
		fcode[i] = (int *) calloc(gnum_ft_conn, sizeof(int));
		for (j = 0; j < gnum_ft_conn; j++) {
			fcode[i][j] = -1;
		}
	}

	/* build the graph up to <layer>
	 */
	for (i = 0; i < gnum_op_conn; i++) {
		tmp = new_IntList(i);
		if (gout_ops) {
			gout_ops->prev = tmp;
		}
		tmp->next = gout_ops;
		gout_ops = tmp;
	}
	for (i = 0; i < ginitial_state.num_F; i++) {
		ft = ginitial_state.F[i];
		gin_ft_count++;
		gft_conn[ft].first_appearance = 0;
		gft_conn[ft].info_at[0] = new_FtLevelInfo();
		tmp = new_IntList(ft);
		tmp->next = gin_fts;
		gin_fts = tmp;
	}
	gin_fts_at[0] = gin_fts;
	if (gcmd_line.display_info) {
		printf("\ntime: %3d, %5d facts and %7d exclusive pairs", 0,
				gin_ft_count, gin_ft_exclusion_count);
		fflush(stdout);
	}
	for (t = 0; t < layer; t++) {
		build_graph_evolution_step();
	}

	printf("\n\ncreating thin gp-based encoding...");

	/* prec constraints, + code assignment.
	 */
	lnum_clauses = 0;
	code = 1; /* variables numbered 1 .. n */
	for (t = 0; t <= layer; t++) {
		printf("\nplan graph layer %d...", t);
		for (i = 0; i < gnum_ft_conn; i++) {
			if (gft_conn[i].info_at[t] == NULL /* equiv to not in here */) {
				continue;
			}
			/* insert adder clause, if at t > 0. else, say it has to be true,
			 * if it's an initial fact.
			 */
			if (t == 0) {
				for (j = 0; j < ginitial_state.num_F; j++) {
					if (ginitial_state.F[j] == i)
						break;
				}
				if (j < ginitial_state.num_F) {
					fcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					fop_to_code[code - 1] = i;
					ftime_to_code[code - 1] = t;
					if (lnum_clauses == MAX_CLAUSES) {
						printf(
								"\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
						exit(1);
					}
					lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
					lclause[lnum_clauses][0] = fcode[t][i];
					lclause_size[lnum_clauses] = 1;

					/* printf("LOCAL 5 (%d): %d \n", lnum_clauses, lclause[lnum_clauses][0]); */
				}
				continue;
			}
			if (fcode[t][i] != -1) {
				printf("\n\nft already coded??\n\n");
				exit(UNSAT);
			}
			fcode[t][i] = code++;
			if (code == MAX_CNF_VARS + 1) {
				printf("\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
				exit(1);
			}
			fop_to_code[code - 1] = i;
			ftime_to_code[code - 1] = t;
			if (lnum_clauses == MAX_CLAUSES) {
				printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
				exit(1);
			}
			lclause[lnum_clauses] = (int *) calloc(gft_conn[i].num_A + 1,
					sizeof(int));
			lclause[lnum_clauses][0] = (-1) * fcode[t][i];
			lclause_size[lnum_clauses] = 1;

			/* Razer - HORN */
			vec_horn[abs(lclause[lnum_clauses][0])] = 1;
			cont_horn++;

			for (j = 0; j < gft_conn[i].num_A; j++) {
				op = gft_conn[i].A[j];
				if (gop_conn[op].info_at[t - 1] == NULL ) {
					continue;
				}
				if (lcode[t - 1][op] == -1) {
					lcode[t - 1][op] = code++;
					if (0) {
						printf("\npC %d at %d", op, t - 1);
					}
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = op;
					ltime_to_code[code - 1] = t - 1;
				}
				/* Razer - para poder gerar MHF */
				lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
						get_action_prop( lcode[t - 1][op] );

				/* Razer - HORN */
				int x = abs(lcode[t - 1][op]);
				/* printf("--PAU lcode[%d][%d] = %d\n", t - 1, op, lcode[t - 1][op]); */
				vec_horn[x] = 1;

			}
			if (lclause_size[lnum_clauses] == 1) {
				printf("\n\nno achiever in at t>0??\n\n");
				exit(UNSAT);
			}
			lnum_clauses++;
		} /* i-ft */

		if (t == layer) {
			continue;
		}

		for (i = 0; i < gnum_op_conn; i++) {
			if (gop_conn[i].info_at[t] == NULL /* equiv to not in here */) {
				continue;
			}
			/* insert prec clauses.
			 */
			for (j = 0; j < gop_conn[i].num_P; j++) {
				ft = gop_conn[i].P[j];

				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
				/* here the op i is used at t, for the 1st time. assign the code.
				 */
				if (j == 0) {
					if (lcode[t][i] != -1) {
						printf("\n\nop code %d at %d already assigned??\n\n", i,
								t);
						exit(UNSAT);
					}
					if (0) {
						printf("\nC %d at %d", i, t);
					}
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}

				/* Razer - para gera MHF */
				lclause[lnum_clauses][0] = get_action_prop( (-1) * lcode[t][i] );
				if (fcode[t][ft] == -1) {
					printf("\n\nprec fact not coded??\n\n");
					exit(1);
				}
				lclause[lnum_clauses][1] = fcode[t][ft];
				lclause_size[lnum_clauses] = 2;

				/* Razer, 2CNF - POSITIVE */
				vec_2cnf[lclause[lnum_clauses][0]] = 1;
				vec_2cnf[lclause[lnum_clauses][1]] = 1;
				cont_2cnf++;

				lnum_clauses++;


			} /* j: pres of i-op */
		} /* i -- op */
	} /* t */

	/* goal constraints
	 */
	printf("\ngoal constraints...");
	for (i = 0; i < ggoal_state.num_F; i++) {
		ft = ggoal_state.F[i];

		if (lnum_clauses == MAX_CLAUSES) {
			printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
			exit(1);
		}
		lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
		if (fcode[layer][ft] == -1) {
			printf("\n\ngoal fact not coded - level too low??\n\n");
			exit(UNSAT);
		}
		lclause[lnum_clauses][0] = fcode[layer][ft];
		lclause_size[lnum_clauses] = 1;
		lnum_clauses++;

		/* Razer */
		vec_unit[abs(fcode[layer][ft])] =  1;
		cont_unit++;
	} /* goals */

	/* exclusion constraints.
	 */

	/* START CHANGE */
	for (t = 0; t <= layer; t++) {
		printf("\nexclusion constraints layer %d...", t);

		for (i1 = gin_fts_at[t]; i1 && i1->next; i1 = i1->next) {
			i = i1->i1;
			for (i2 = i1->next; i2; i2 = i2->next) {
				j = i2->i1;
				if (!(gft_conn[i].info_at[t]->bit_exclusives[gft_conn[j].uid_block]
						& gft_conn[j].uid_mask)) {
					continue;
				}
				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
				if (fcode[t][i] == -1) {
					fcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					fop_to_code[code - 1] = i;
					ftime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][0] = (-1) * fcode[t][i];
				if (fcode[t][j] == -1) {
					fcode[t][j] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					fop_to_code[code - 1] = j;
					ftime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][1] = (-1) * fcode[t][j];
				lclause_size[lnum_clauses] = 2;

				/* Razer, 2CNF - NEGATIVE --- HORN */
				vec_horn[abs(lclause[lnum_clauses][0])] = 1;
				vec_horn[abs(lclause[lnum_clauses][1])] = 1;
				cont_horn++;

				lnum_clauses++;

			} /* i2 */
		} /* i1 */

		if (t == layer)
			continue;
		/* END CHANGE */

		for (i1 = gin_ops_at[t]; i1 && i1->next; i1 = i1->next) {
			i = i1->i1;
			for (i2 = i1->next; i2; i2 = i2->next) {
				j = i2->i1;
				if (!interfere(i, j)) {
					continue;
				}
				if (lnum_clauses == MAX_CLAUSES) {
					printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
					exit(1);
				}
				lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
				if (lcode[t][i] == -1) {
					lcode[t][i] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = i;
					ltime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][0] = get_action_prop( (-1) * lcode[t][i] );
				if (lcode[t][j] == -1) {
					lcode[t][j] = code++;
					if (code == MAX_CNF_VARS + 1) {
						printf(
								"\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
						exit(1);
					}
					lop_to_code[code - 1] = j;
					ltime_to_code[code - 1] = t;
				}
				lclause[lnum_clauses][1] = get_action_prop( (-1) * lcode[t][j] );
				lclause_size[lnum_clauses] = 2;

				/* Razer, 2CNF - POSITIVE */
				vec_2cnf[abs(lclause[lnum_clauses][0])] = 1;
				vec_2cnf[abs(lclause[lnum_clauses][1])] = 1;
				cont_2cnf++;

				lnum_clauses++;
			}
		}
	}

	/* that's it. print CNF file.
	 */
	/* Start timer */
	clock_t start, end, send, sstart;
	double execution_time, s_time;
	start = clock();	
	
	if (gcmd_line.debug) {
		/* debugging: print semantic version of clause set.
		 */

		if ((VARFILE = fopen(gcmd_line.varFileName, "w")) == NULL ) {
			printf("\n\nEXIT: can't open VARFILE file.\n\n");
			exit(1);
		}
		fprintf(VARFILE, "\n\nc DECISION LAYER %d, THIN GP-BASED ENCODING.",
				layer);
		fprintf(VARFILE, "\n\nc VARS:");

		for (i = 1; i < code; i++) {
			fprintf(VARFILE, "\nc var %2d action (", i);
			print_op_nameToFile(lop_to_code[i], VARFILE);
			fprintf(VARFILE, ") %d", ltime_to_code[i]);
		}

		/*
		 printf("\n\nCLAUSES:");
		 for ( i = 0; i < lnum_clauses; i++ ) {
		 printf("\n%6d - ", i);
		 if ( 1 ) {
		 for ( j = 0; j < lclause_size[i]; j++ ) {
		 printf("(%d)", lclause[i][j]);
		 if ( j < lclause_size[i]-1 ) printf(", ");
		 }
		 fflush(stdout);
		 }
		 for ( j = 0; j < lclause_size[i]; j++ ) {
		 if ( lclause[i][j] > 0 ) {
		 printf("(");
		 print_op_name( lop_to_code[lclause[i][j]] );
		 printf(" at %d)", ltime_to_code[lclause[i][j]] );
		 } else {
		 printf("(NOT ");
		 print_op_name( lop_to_code[(-1)*lclause[i][j]] );
		 printf(" at %d)", ltime_to_code[(-1)*lclause[i][j]] );
		 }
		 if ( j < lclause_size[i]-1 ) printf(", ");
		 }
		 }
		 */
		fclose(VARFILE);
	}

	int added_neg = 0;
	int added_pos = 0;

	if (create == 0) {
		if ((CNF = fopen(gcmd_line.cnfFileName, "w")) == NULL ) {
			printf("\n\ncan't open CNF file.\n\n");
			exit(1);
		}

		if (gcmd_line.makeMHF == 1) {

			if (gcmd_line.makePURE == 1) {
				/* TODO fazer o calculo dos literais enquanto gera as clausulas, para ser
				 mais rapido */
/*

				for (i = 0; i < lnum_clauses; i++) {
					if (lclause_size[i] == 2) {
						if (lclause[i][0] > 0) {

							for (j = 0; j < lclause_size[i]; j++) {
								int x = abs(lclause[i][j]);
								vec_2cnf[x] = 1;
							}
							cont_2cnf++;
						}
						else {

							for (j = 0; j < lclause_size[i]; j++) {
								int x = abs(lclause[i][j]);
								vec_horn[x] = 1;
							}
							cont_horn++;
						}
					}
					else if (lclause_size[i] > 2) {

						for (j = 0; j < lclause_size[i]; j++) {
							int x = abs(lclause[i][j]);
							vec_horn[x] = 1;
						}
						cont_horn++;
					}
					else if (lclause_size[i] == 1) {
						int x = abs(lclause[i][0]);
						vec_unit[x] = 1;
						cont_unit++;
					}
				}
				printf("start generating: unit: %d - 2cnf: %d - horn: %d\n", cont_unit, cont_2cnf, cont_horn); */
				for (i=1; i<=code; i++) {
					/* printf("   var: %d h[%d] 2[%d] u[%d]\n", i, vec_horn[i], vec_2cnf[i], vec_unit[i]); */
					if (vec_unit[i]==1) {
						/* eh unitaria */
						continue;
					}
					else {
						if (vec_horn[i]==1 && vec_2cnf[i]==0) {
							/* So aparece na horn */
							lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
							lclause[lnum_clauses][0] = -1 * i;
							lclause_size[lnum_clauses] = 1;
							lnum_clauses++;
							added_neg++;
							cont_unit++;
						}
						else if (vec_horn[i]==0 && vec_2cnf[i]==1) {
							/* So aparece na 2cnf */
							lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
							lclause[lnum_clauses][0] = i;
							lclause_size[lnum_clauses] = 1;
							lnum_clauses++;
							added_pos++;
							cont_unit++;
						}
					}

				}
			}
			printf(
					"\n\nDECISION LAYER %d, WRITING THIN GP-BASED ENCODING WITH %d VARS, %d CLAUSES.\n",
					layer, code - 1, lnum_clauses);


			if (gcmd_line.makePURE == 1)
				printf("\nGenerated: pos: %d - neg: %d", added_pos, added_neg);

			printf("\nUnit: %d (%f %%) - 2CNF: %d (%f %%) - HORN: %d (%f %%)\n\n", cont_unit, ((double)cont_unit/lnum_clauses)*100,
																					cont_2cnf, ((double)cont_2cnf/lnum_clauses)*100,
																					cont_horn, ((double)cont_horn/lnum_clauses)*100);

			printf("start writing\n");

			/** tirar **/
			/*for (i = 0; i < lnum_clauses; i++) {
				if (lclause_size[i] == 1) {
					printf(" unit: %d\n ", lclause[i][0]);
				}
			}*/

		if (gcmd_line.makePBS == 1) {
     		fprintf(CNF, "* #variable= %d #constraint= %d\n", code - 1, lnum_clauses);

			for (i = 0; i < lnum_clauses; i++) {
					for (j = 0; j < lclause_size[i]; j++) {
							if (lclause[i][j] < 0)
									fprintf(CNF, "+1 ~x%d ", -1*lclause[i][j]);
							else
									fprintf(CNF, "+1 x%d ", lclause[i][j]);
					}
					fprintf(CNF, ">= 1;\n");
			}
		}

			/* Razer - generate prefs */
			if (gcmd_line.makePREFS == 1) {
				/* the first variable or 2 CNF POSITIVE is generated as prefs.txt */
				FILE *prefs;

				if ((prefs = fopen("prefs.txt", "w")) == NULL ) {
					printf("\n\ncan't open PREFS file.\n\n");
					exit(1);
				}

				i = 0;
				while (!vec_2cnf[i++]);

				fprintf(prefs, "%d\n", i-1);

				fclose(prefs);


			}
		}
		else {
				if (gcmd_line.makePBS == 1) {
						fprintf(CNF, "* #variable= %d #constraint= %d\n", code - 1, lnum_clauses);

						for (i = 0; i < lnum_clauses; i++) {
								for (j = 0; j < lclause_size[i]; j++) {
										if (lclause[i][j] < 0)
												fprintf(CNF, "+1 ~x%d ", -1*lclause[i][j]);
										else
												fprintf(CNF, "+1 x%d ", lclause[i][j]);
								}
								fprintf(CNF, ">= 1;\n");
						}
				}
				else {
					if (gcmd_line.makeISCAS == 1) {
			
						int* vec_vars;
						vec_vars = (int*)malloc((code) * sizeof(int));
						memset(vec_vars, 0, (code));
			
						for (i = 0; i < lnum_clauses; i++) {
								for (j = 0; j < lclause_size[i]; j++) {
										if (lclause[i][j] < 0)
												vec_vars[-1*lclause[i][j]] = 1;
										else
												vec_vars[lclause[i][j]] = 1;
								}
						}
						
						for (i=0; i<code; i++) {
			   				if (vec_vars[i]) {
			 					fprintf(CNF, "INPUT(V%d)\n", i);	
							}
						}
						for (i=0; i<code; i++) {
			   				if (vec_vars[i]) {
			 					fprintf(CNF, "NV%d=NOT(V%d)\n", i, i);	
							}
						}
						for (i = 0; i < lnum_clauses; i++) {
							if (lclause_size[i]==1) {
								if (lclause[i][0]<0) {
		    						fprintf(CNF, "CL%d=BUFF(NV%d)\n", i, -1*lclause[i][0]);	
								}
								else {
		    						fprintf(CNF, "CL%d=BUFF(V%d)\n", i, lclause[i][0]);	
								}
							}
							else {
		    					fprintf(CNF, "CL%d=OR(", i);	
								for (j = 0; j < lclause_size[i]; j++) {
									if (lclause[i][j] < 0)
											fprintf(CNF, "NV%d", -1*lclause[i][j]);
									else
											fprintf(CNF, "V%d", lclause[i][j]);
									if (j != lclause_size[i] - 1)
										fprintf(CNF, ", ");
								}
								fprintf(CNF, ")\n");
							}
						}
		   				fprintf(CNF, "RES=AND(");	
						for (i = 0; i < lnum_clauses; i++) {
							fprintf(CNF, "CL%d", i);
							if (i != lnum_clauses - 1)
								fprintf(CNF, ", ");
						}
						fprintf(CNF, ")\n");
		    			fprintf(CNF, "OUTPUT(RES)\n");
					}
					else {

						printf(
										"\n\nDECISION LAYER %d, WRITING THIN GP-BASED ENCODING WITH %d VARS, %d CLAUSES.\n",
										layer, code - 1, lnum_clauses);

						fprintf(CNF,
										"c CNF file planning task -p %s, -o %s, -f %s, bound %d, thin gp-based encoding\n",
										gcmd_line.path, gcmd_line.ops_file_name,
										gcmd_line.fct_file_name, layer);

						fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);

						sstart = clock();


						for (i = 0; i < lnum_clauses; i++) {
									for (j = 0; j < lclause_size[i]; j++) {
											fprintf(CNF, "%d ", lclause[i][j]);
									}
									fprintf(CNF, "0\n");
							} 
							

						// const int BUFFER_SIZE = 1024;
						// char buffer[BUFFER_SIZE];
						// int i, j;
						// int pos = 0;

						// for (i = 0; i < lnum_clauses; i++)
						// {
						// 	for (j = 0; j < lclause_size[i]; j++)
						// 	{
						// 		pos += sprintf(&buffer[pos], "%d ", lclause[i][j]);
						// 		if (pos >= BUFFER_SIZE - 10)
						// 		{
						// 			fwrite(buffer, pos, sizeof(char), CNF);
						// 			pos = 0;
						// 		}
						// 	}
						// 	pos += sprintf(&buffer[pos], "0\n");
						// 	if (pos >= BUFFER_SIZE - 10)
						// 	{
						// 		fwrite(buffer, pos, sizeof(char), CNF);
						// 		pos = 0;
						// 	}
						// }

						// if (pos > 0)
						// {
						// 	fwrite(buffer, pos, sizeof(char), CNF);
						// }
						send = clock();
					}
				}

		fclose(CNF);

		/* Razer - generate prefs */
		if (gcmd_line.makePREFS == 1) {
			/* the first variable or 2 CNF POSITIVE is generated as prefs.txt */
			FILE *prefs;

			if ((prefs = fopen("prefs.txt", "w")) == NULL ) {
				printf("\n\ncan't open PREFS file.\n\n");
				exit(1);
			}

			i = 0;
			for (i=0; i<code; i++) {
			   if (vec_2cnf[i]) {
					fprintf(prefs, "%d\n", i);
				}
			}

			fclose(prefs);

        }

		FILE *LITS;
		if ((LITS = fopen("lits.txt", "w")) == NULL ) {
			printf("\n\nEXIT: can't open LITS file.\n\n");

		}
		else {
			for (i=1; i<=code; i++) {
				/* operador */
				int oper = lop_to_code[i];
				if (oper != 0) {
/*					fprintf(LITS, "%d - %s - OPER\n", i, goperators[gop_conn[oper].op]->name); */
					fprintf(LITS, "%d - OPER\n", i);
				}
				else {
					/* fato */
					/* fprintf(LITS, "%s - FACT\n", goperators[gop_conn[fop_to_code[i]].op]->name); */
				}
			}
			fclose(LITS);
		}
	}

	}
	/* end timer */
		end = clock();
		execution_time = ((double)(end - start))/CLOCKS_PER_SEC;
		s_time = ((double)(send - sstart))/CLOCKS_PER_SEC;
		printf("\n=======NEW================================================\n");
		printf("\nExectuion time: %fs\n", execution_time);
		printf("\nSpecific time: %fs\n", s_time);
		printf("\n=======================================================\n");
}

/*
   Razer e Bruno 2015 - codificacao em pseudo-boolean compactada
*/
void print_thin_gp_based_encoding_PBS2(int layer, int create)

{
  FILE *CNF, *VARFILE;

  int i, j, t, ft, op, code;
  IntList *tmp, *i1, *i2;

  /* have to separate the ft coding out from the op coding.
   */
  int **fcode;
  int *fop_to_code;
  int *ftime_to_code;


  /* Razer, para gerar MHF com pure literals */
  /* Razer, para gerar também PBS compactado */
  int cont_2cnf = 0;
  int cont_horn = 0;
  int cont_unit = 0;
  char* vec_2cnf;
  char* vec_horn;
  char* vec_unit;

  /* lista de clausulas pb compactadas */
  int **lclause_pb_comp;
  int *lclause_size_pb_comp;
  int lnum_clauses_pb_comp = 0;

  int *temp_clause;  /* clausula pb temporaria */
  temp_clause = (char*)malloc((MAX_CNF_VARS) * sizeof(char));

  lclause_pb_comp = (int **) calloc(MAX_CLAUSES, sizeof(int *));
  lclause_size_pb_comp = (int *) calloc(MAX_CLAUSES, sizeof(int));



  vec_2cnf = (char*)malloc((MAX_CLAUSES) * sizeof(char));
  vec_horn = (char*)malloc((MAX_CLAUSES) * sizeof(char));
  vec_unit = (char*)malloc((MAX_CLAUSES) * sizeof(char));


  memset(vec_2cnf, 0, (MAX_CLAUSES));
  memset(vec_horn, 0, (MAX_CLAUSES));
  memset(vec_unit, 0, (MAX_CLAUSES));




  lclause = (int **) calloc(MAX_CLAUSES, sizeof(int *));
  lclause_size = (int *) calloc(MAX_CLAUSES, sizeof(int));
  lcode = (int **) calloc(layer, sizeof(int *));
  lop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
  ltime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
  for (i = 0; i < layer; i++) {
    lcode[i] = (int *) calloc(gnum_op_conn, sizeof(int));
    for (j = 0; j < gnum_op_conn; j++) {
      lcode[i][j] = -1;
    }
  }
  fcode = (int **) calloc(layer + 1, sizeof(int *));
  fop_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
  ftime_to_code = (int *) calloc(MAX_CNF_VARS, sizeof(int));
  for (i = 0; i <= layer; i++) {
    fcode[i] = (int *) calloc(gnum_ft_conn, sizeof(int));
    for (j = 0; j < gnum_ft_conn; j++) {
      fcode[i][j] = -1;
    }
  }

  /* build the graph up to <layer>
   */
  for (i = 0; i < gnum_op_conn; i++) {
    tmp = new_IntList(i);
    if (gout_ops) {
      gout_ops->prev = tmp;
    }
    tmp->next = gout_ops;
    gout_ops = tmp;
  }
  for (i = 0; i < ginitial_state.num_F; i++) {
    ft = ginitial_state.F[i];
    gin_ft_count++;
    gft_conn[ft].first_appearance = 0;
    gft_conn[ft].info_at[0] = new_FtLevelInfo();
    tmp = new_IntList(ft);
    tmp->next = gin_fts;
    gin_fts = tmp;
  }
  gin_fts_at[0] = gin_fts;
  if (gcmd_line.display_info) {
    printf("\ntime: %3d, %5d facts and %7d exclusive pairs", 0,
        gin_ft_count, gin_ft_exclusion_count);
    fflush(stdout);
  }
  for (t = 0; t < layer; t++) {
    build_graph_evolution_step();
  }

  printf("\n\ncreating thin gp-based encoding PBS2...");

  /* prec constraints, + code assignment.
   */
  lnum_clauses = 0;
  code = 1; /* variables numbered 1 .. n */
  for (t = 0; t <= layer; t++) {
    printf("\nplan graph layer %d...", t);
    for (i = 0; i < gnum_ft_conn; i++) {
      if (gft_conn[i].info_at[t] == NULL /* equiv to not in here */) {
        continue;
      }
      /* insert adder clause, if at t > 0. else, say it has to be true,
       * if it's an initial fact.
       */
      if (t == 0) {
        for (j = 0; j < ginitial_state.num_F; j++) {
          if (ginitial_state.F[j] == i)
            break;
        }
        if (j < ginitial_state.num_F) {
          fcode[t][i] = code++;
          if (code == MAX_CNF_VARS + 1) {
            printf(
                "\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
            exit(1);
          }
          fop_to_code[code - 1] = i;
          ftime_to_code[code - 1] = t;
          if (lnum_clauses == MAX_CLAUSES) {
            printf(
                "\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
            exit(1);
          }
          lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
          lclause[lnum_clauses][0] = fcode[t][i];
          lclause_size[lnum_clauses] = 1;

          /* printf("LOCAL 5 (%d): %d \n", lnum_clauses, lclause[lnum_clauses][0]); */
        }
        continue;
      }
      if (fcode[t][i] != -1) {
        printf("\n\nft already coded??\n\n");
        exit(UNSAT);
      }
      fcode[t][i] = code++;
      if (code == MAX_CNF_VARS + 1) {
        printf("\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
        exit(1);
      }
      fop_to_code[code - 1] = i;
      ftime_to_code[code - 1] = t;
      if (lnum_clauses == MAX_CLAUSES) {
        printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
        exit(1);
      }
      lclause[lnum_clauses] = (int *) calloc(gft_conn[i].num_A + 1,
          sizeof(int));
      lclause[lnum_clauses][0] = (-1) * fcode[t][i];
      lclause_size[lnum_clauses] = 1;

      /* Razer - HORN */
      vec_horn[abs(lclause[lnum_clauses][0])] = 1;
      cont_horn++;

      for (j = 0; j < gft_conn[i].num_A; j++) {
        op = gft_conn[i].A[j];
        if (gop_conn[op].info_at[t - 1] == NULL ) {
          continue;
        }
        if (lcode[t - 1][op] == -1) {
          lcode[t - 1][op] = code++;
          if (0) {
            printf("\npC %d at %d", op, t - 1);
          }
          if (code == MAX_CNF_VARS + 1) {
            printf(
                "\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
            exit(1);
          }
          lop_to_code[code - 1] = op;
          ltime_to_code[code - 1] = t - 1;
        }
        /* Razer - para poder gerar MHF */
        lclause[lnum_clauses][lclause_size[lnum_clauses]++] =
          get_action_prop( lcode[t - 1][op] );

        /* Razer - HORN */
        int x = abs(lcode[t - 1][op]);
        /* printf("--PAU lcode[%d][%d] = %d\n", t - 1, op, lcode[t - 1][op]); */
        vec_horn[x] = 1;

      }
      if (lclause_size[lnum_clauses] == 1) {
        printf("\n\nno achiever in at t>0??\n\n");
        exit(UNSAT);
      }
      lnum_clauses++;
    } /* i-ft */

    if (t == layer) {
      continue;
    }

    for (i = 0; i < gnum_op_conn; i++) {
      if (gop_conn[i].info_at[t] == NULL /* equiv to not in here */) {
        continue;
      }
      /* insert prec clauses.
       */
      for (j = 0; j < gop_conn[i].num_P; j++) {
        ft = gop_conn[i].P[j];

        if (lnum_clauses == MAX_CLAUSES) {
          printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
          exit(1);
        }
        lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
        /* here the op i is used at t, for the 1st time. assign the code.
         */
        if (j == 0) {
          if (lcode[t][i] != -1) {
            printf("\n\nop code %d at %d already assigned??\n\n", i,
                t);
            exit(UNSAT);
          }
          if (0) {
            printf("\nC %d at %d", i, t);
          }
          lcode[t][i] = code++;
          if (code == MAX_CNF_VARS + 1) {
            printf(
                "\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
            exit(1);
          }
          lop_to_code[code - 1] = i;
          ltime_to_code[code - 1] = t;
        }

        /* Razer - para gera MHF */
        lclause[lnum_clauses][0] = get_action_prop( (-1) * lcode[t][i] );
        if (fcode[t][ft] == -1) {
          printf("\n\nprec fact not coded??\n\n");
          exit(1);
        }
        lclause[lnum_clauses][1] = fcode[t][ft];
        lclause_size[lnum_clauses] = 2;

        /* Razer, 2CNF - POSITIVE */
        vec_2cnf[lclause[lnum_clauses][0]] = 1;
        vec_2cnf[lclause[lnum_clauses][1]] = 1;
        cont_2cnf++;

        lnum_clauses++;


      } /* j: pres of i-op */
    } /* i -- op */
  } /* t */

  printf("\nlayers terminated...");

  /* goal constraints
   */
  printf("\ngoal constraints...");
  for (i = 0; i < ggoal_state.num_F; i++) {
    ft = ggoal_state.F[i];

    if (lnum_clauses == MAX_CLAUSES) {
      printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
      exit(1);
    }
    lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
    if (fcode[layer][ft] == -1) {
      printf("\n\ngoal fact not coded - level too low??\n\n");
      exit(UNSAT);
    }
    lclause[lnum_clauses][0] = fcode[layer][ft];
    lclause_size[lnum_clauses] = 1;
    lnum_clauses++;

    /* Razer */
    vec_unit[abs(fcode[layer][ft])] =  1;
    cont_unit++;
  } /* goals */

  /* exclusion constraints.
   */

  /* START CHANGE */
  /* Razer - Clausulas do tipo 8 */
  int ind_pb_comp = 0;     /* indice da clausula pb compactada */
  int cont_pb_comp = 0;    /* quantidade de clausulas pb compactadas */
  int aux1 = 0;

  for (t = 0; t <= layer; t++) {
    printf("\nexclusion constraints layer %d...", t);

    for (i1 = gin_fts_at[t]; i1 && i1->next; i1 = i1->next) {
      i = i1->i1;

      /* Razer e Bruno - tamanho da clausula PB compcatada atual = 0 */
      int tam_curr_clause = 0;

      /* Razer e Bruno - laço de todos os mutex com i, gera uma clausula só */
      for (i2 = i1->next; i2; i2 = i2->next) {


        j = i2->i1;
        if (!(gft_conn[i].info_at[t]->bit_exclusives[gft_conn[j].uid_block]
              & gft_conn[j].uid_mask)) {
          continue;
        }


        if (lnum_clauses == MAX_CLAUSES) {
          printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
          exit(1);
        }


        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS != 2) {
          lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
        }



        if (fcode[t][i] == -1) {
          fcode[t][i] = code++;
          if (code == MAX_CNF_VARS + 1) {
            printf(
                "\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
            exit(1);
          }
          fop_to_code[code - 1] = i;
          ftime_to_code[code - 1] = t;
        }



        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS != 2) {
          lclause[lnum_clauses][0] = (-1) * fcode[t][i];
        }



        if (fcode[t][j] == -1) {
          fcode[t][j] = code++;
          if (code == MAX_CNF_VARS + 1) {
            printf(
                "\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
            exit(1);
          }
          fop_to_code[code - 1] = j;
          ftime_to_code[code - 1] = t;
        }


        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS != 2) {
          lclause[lnum_clauses][1] = (-1) * fcode[t][j];
          lclause_size[lnum_clauses] = 2;
        }


        /* Razer, 2CNF - NEGATIVE --- HORN */
        /*vec_horn[abs(lclause[lnum_clauses][0])] = 1;
          vec_horn[abs(lclause[lnum_clauses][1])] = 1;*/
        vec_horn[abs(fcode[t][i])] = 1;
        vec_horn[abs(fcode[t][j])] = 1;
        cont_horn++;

        /* Razer i com j
           i = lclause[lnum_clauses][0]
           j = lclause[lnum_clauses][1] 

           adicionar à lista para gerar posteriormente
         */

        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS == 2) {
          if (tam_curr_clause == 0 ) {
            tam_curr_clause = 2;
            /*temp_clause[0] = lclause[lnum_clauses][0];*/
            /*temp_clause[1] = lclause[lnum_clauses][1];*/
            temp_clause[0] = (-1) * fcode[t][i];
            temp_clause[1] = (-1) * fcode[t][j];
          }
          else {
            /* so adiciona a [1] pq a [0] é sempre a mesma - indice i */
            /* temp_clause[tam_curr_clause] = lclause[lnum_clauses][1];*/
            temp_clause[tam_curr_clause] = (-1) * fcode[t][j];
            tam_curr_clause++;
          } 
        }


        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS != 2) {
          lnum_clauses++;
        }

      } /* i2 */
      /* Razer - gera a cláusula pb compactada */

      if (tam_curr_clause > 0 ) {
        lclause_pb_comp[lnum_clauses_pb_comp] = (int *) calloc(tam_curr_clause, sizeof(int));
        int aux;
        for (aux=0; aux<tam_curr_clause; aux++) {
          lclause_pb_comp[lnum_clauses_pb_comp][aux] = temp_clause[aux];
        }
        lclause_size_pb_comp[lnum_clauses_pb_comp] = tam_curr_clause;
        lnum_clauses_pb_comp++;
      }
      tam_curr_clause = 0;

    } /* i1 */

    if (t == layer)
      continue;
    /* END CHANGE */


    /* Razer e Bruno - Cláusulas 7.1 e 7.2 - de acoes */
    int tam_curr_clause = 0;

    for (i1 = gin_ops_at[t]; i1 && i1->next; i1 = i1->next) {
      i = i1->i1;

      /* Razer e Bruno - tamanho da clausula PB compcatada atual = 0 */
      tam_curr_clause = 0;

      for (i2 = i1->next; i2; i2 = i2->next) {
        j = i2->i1;
        if (!interfere(i, j)) {
          continue;
        }
        /* Razer e Bruno - TODO no futuro validar também a quantidade de cláusulas compactas */
        if (lnum_clauses == MAX_CLAUSES) {
          printf("\n\ntoo many clauses. increase MAX_CLAUSES.\n\n");
          exit(1);
        }

        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS != 2) {
          lclause[lnum_clauses] = (int *) calloc(2, sizeof(int));
        }

        if (lcode[t][i] == -1) {
          lcode[t][i] = code++;
          if (code == MAX_CNF_VARS + 1) {
            printf(
                "\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
            exit(1);
          }
          lop_to_code[code - 1] = i;
          ltime_to_code[code - 1] = t;
        }


        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS != 2) {
          lclause[lnum_clauses][0] = get_action_prop( (-1) * lcode[t][i] );
        }

        if (lcode[t][j] == -1) {
          lcode[t][j] = code++;
          if (code == MAX_CNF_VARS + 1) {
            printf(
                "\n\ntoo many cnf vars. increase MAX_CNF_VARS.\n\n");
            exit(1);
          }
          lop_to_code[code - 1] = j;
          ltime_to_code[code - 1] = t;
        }

        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS != 2) {
          lclause[lnum_clauses][1] = get_action_prop( (-1) * lcode[t][j] );
          lclause_size[lnum_clauses] = 2;
        }

        /* Razer, 2CNF - POSITIVE */
        /*vec_2cnf[abs(lclause[lnum_clauses][0])] = 1;
          vec_2cnf[abs(lclause[lnum_clauses][1])] = 1; */

        vec_2cnf[abs(lcode[t][i])] = 1;
        vec_2cnf[abs(lcode[t][j])] = 1;

        cont_2cnf++;


        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS == 2) {
          if (tam_curr_clause == 0 ) {
            tam_curr_clause = 2;
            /*temp_clause[0] = lclause[lnum_clauses][0];*/
            /*temp_clause[1] = lclause[lnum_clauses][1];*/
            temp_clause[0] = get_action_prop( (-1) * lcode[t][i] );
            temp_clause[1] = get_action_prop( (-1) * lcode[t][j] );
          }
          else {
            /* so adiciona a [1] pq a [0] é sempre a mesma - indice i */
            /* temp_clause[tam_curr_clause] = lclause[lnum_clauses][1];*/
            temp_clause[tam_curr_clause] = get_action_prop( (-1) * lcode[t][j] );
            tam_curr_clause++;
          }
        }


        /* Razer e Bruno - se for PBS2, nao gera a clausula normal, pq vai gerar compactada */
        if (gcmd_line.makePBS != 2) {
          lnum_clauses++;
        }

      }

      /* Razer - gera a cláusula pb compactada */

      if (tam_curr_clause > 0 ) {
        lclause_pb_comp[lnum_clauses_pb_comp] = (int *) calloc(tam_curr_clause, sizeof(int));
        int aux;
        for (aux=0; aux<tam_curr_clause; aux++) {
          lclause_pb_comp[lnum_clauses_pb_comp][aux] = temp_clause[aux];
        }
        lclause_size_pb_comp[lnum_clauses_pb_comp] = tam_curr_clause;
        lnum_clauses_pb_comp++;
      }
      tam_curr_clause = 0;

    }
  }

  /* that's it. print CNF file.
   */
  if (gcmd_line.debug) {
    /* debugging: print semantic version of clause set.
     */

    if ((VARFILE = fopen(gcmd_line.varFileName, "w")) == NULL ) {
      printf("\n\nEXIT: can't open VARFILE file.\n\n");
      exit(1);
    }
    fprintf(VARFILE, "\n\nc DECISION LAYER %d, THIN GP-BASED ENCODING.",
        layer);
    fprintf(VARFILE, "\n\nc VARS:");

    for (i = 1; i < code; i++) {
      fprintf(VARFILE, "\nc var %2d action (", i);
      print_op_nameToFile(lop_to_code[i], VARFILE);
      fprintf(VARFILE, ") %d", ltime_to_code[i]);
    }

    /*
       printf("\n\nCLAUSES:");
       for ( i = 0; i < lnum_clauses; i++ ) {
       printf("\n%6d - ", i);
       if ( 1 ) {
       for ( j = 0; j < lclause_size[i]; j++ ) {
       printf("(%d)", lclause[i][j]);
       if ( j < lclause_size[i]-1 ) printf(", ");
       }
       fflush(stdout);
       }
       for ( j = 0; j < lclause_size[i]; j++ ) {
       if ( lclause[i][j] > 0 ) {
       printf("(");
       print_op_name( lop_to_code[lclause[i][j]] );
       printf(" at %d)", ltime_to_code[lclause[i][j]] );
       } else {
       printf("(NOT ");
       print_op_name( lop_to_code[(-1)*lclause[i][j]] );
       printf(" at %d)", ltime_to_code[(-1)*lclause[i][j]] );
       }
       if ( j < lclause_size[i]-1 ) printf(", ");
       }
       }
     */
    fclose(VARFILE);
  }

  int added_neg = 0;
  int added_pos = 0;

  if (create == 0) {
    if ((CNF = fopen(gcmd_line.cnfFileName, "w")) == NULL ) {
      printf("\n\ncan't open CNF file.\n\n");
      exit(1);
    }

    if (gcmd_line.makeMHF == 1) {

      if (gcmd_line.makePURE == 1) {
        /* TODO fazer o calculo dos literais enquanto gera as clausulas, para ser
           mais rapido */
        /*

           for (i = 0; i < lnum_clauses; i++) {
           if (lclause_size[i] == 2) {
           if (lclause[i][0] > 0) {

           for (j = 0; j < lclause_size[i]; j++) {
           int x = abs(lclause[i][j]);
           vec_2cnf[x] = 1;
           }
           cont_2cnf++;
           }
           else {

           for (j = 0; j < lclause_size[i]; j++) {
           int x = abs(lclause[i][j]);
           vec_horn[x] = 1;
           }
           cont_horn++;
           }
           }
           else if (lclause_size[i] > 2) {

           for (j = 0; j < lclause_size[i]; j++) {
           int x = abs(lclause[i][j]);
           vec_horn[x] = 1;
           }
           cont_horn++;
           }
           else if (lclause_size[i] == 1) {
           int x = abs(lclause[i][0]);
           vec_unit[x] = 1;
           cont_unit++;
           }
           }
           printf("start generating: unit: %d - 2cnf: %d - horn: %d\n", cont_unit, cont_2cnf, cont_horn); */
        for (i=1; i<=code; i++) {
          /* printf("   var: %d h[%d] 2[%d] u[%d]\n", i, vec_horn[i], vec_2cnf[i], vec_unit[i]); */
          if (vec_unit[i]==1) {
            /* eh unitaria */
            continue;
          }
          else {
            if (vec_horn[i]==1 && vec_2cnf[i]==0) {
              /* So aparece na horn */
              lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
              lclause[lnum_clauses][0] = -1 * i;
              lclause_size[lnum_clauses] = 1;
              lnum_clauses++;
              added_neg++;
              cont_unit++;
            }
            else if (vec_horn[i]==0 && vec_2cnf[i]==1) {
              /* So aparece na 2cnf */
              lclause[lnum_clauses] = (int *) calloc(1, sizeof(int));
              lclause[lnum_clauses][0] = i;
              lclause_size[lnum_clauses] = 1;
              lnum_clauses++;
              added_pos++;
              cont_unit++;
            }
          }

        }
      }
      printf(
          "\n\nDECISION LAYER %d, WRITING THIN GP-BASED ENCODING WITH %d VARS, %d CLAUSES.\n",
          layer, code - 1, lnum_clauses);


      if (gcmd_line.makePURE == 1)
        printf("\nGenerated: pos: %d - neg: %d", added_pos, added_neg);

      printf("\nUnit: %d (%f %%) - 2CNF: %d (%f %%) - HORN: %d (%f %%)\n\n", cont_unit, ((double)cont_unit/lnum_clauses)*100,
          cont_2cnf, ((double)cont_2cnf/lnum_clauses)*100,
          cont_horn, ((double)cont_horn/lnum_clauses)*100);

      printf("start writing\n");

      /** tirar **/
      /*for (i = 0; i < lnum_clauses; i++) {
        if (lclause_size[i] == 1) {
        printf(" unit: %d\n ", lclause[i][0]);
        }
        }*/

      if (gcmd_line.makePBS == 1) {
        fprintf(CNF, "* #variable= %d #constraint= %d\n", code - 1, lnum_clauses);

        for (i = 0; i < lnum_clauses; i++) {
          for (j = 0; j < lclause_size[i]; j++) {
            if (lclause[i][j] < 0)
              fprintf(CNF, "+1 ~x%d ", -1*lclause[i][j]);
            else
              fprintf(CNF, "+1 x%d ", lclause[i][j]);
          }
          fprintf(CNF, ">= 1;\n");
        }
      }

      /* Razer - generate prefs */
      if (gcmd_line.makePREFS == 1) {
        /* the first variable or 2 CNF POSITIVE is generated as prefs.txt */
        FILE *prefs;

        if ((prefs = fopen("prefs.txt", "w")) == NULL ) {
          printf("\n\ncan't open PREFS file.\n\n");
          exit(1);
        }

        i = 0;
        while (!vec_2cnf[i++]);

        fprintf(prefs, "%d\n", i-1);

        fclose(prefs);


      }
    }
    else {
      if (gcmd_line.makePBS == 1) {
        fprintf(CNF, "* #variable= %d #constraint= %d\n", code - 1, lnum_clauses);

        for (i = 0; i < lnum_clauses; i++) {
          for (j = 0; j < lclause_size[i]; j++) {
            if (lclause[i][j] < 0)
              fprintf(CNF, "+1 ~x%d ", -1*lclause[i][j]);
            else
              fprintf(CNF, "+1 x%d ", lclause[i][j]);
          }
          fprintf(CNF, ">= 1;\n");
        }
      }
      else if (gcmd_line.makePBS == 2) {
        fprintf(CNF, "* #variable= %d #constraint= %d\n", code - 1, lnum_clauses+lnum_clauses_pb_comp);

        /* gera cláusulas PBS direto do CNF */
        for (i = 0; i < lnum_clauses; i++) {
          for (j = 0; j < lclause_size[i]; j++) {
            if (lclause[i][j] < 0)
              fprintf(CNF, "+1 ~x%d ", -1*lclause[i][j]);
            else
              fprintf(CNF, "+1 x%d ", lclause[i][j]);
          }
          fprintf(CNF, ">= 1;\n");
        }

        /* Razer e Bruno - gera cláusulas PBS compactadas */
        fprintf(CNF, "* COMPAC\n");
        int peso = 1;
        for (i = 0; i < lnum_clauses_pb_comp; i++) {
          for (j = 0; j < lclause_size_pb_comp[i]; j++) {
            peso =  (j==0) ? (lclause_size_pb_comp[i]-1) : 1 ;
            if (lclause_pb_comp[i][j] < 0)
              fprintf(CNF, "+%d ~x%d ", peso, -1*lclause_pb_comp[i][j]);
            else
              fprintf(CNF, "+%d x%d ", peso, lclause_pb_comp[i][j]);
          }
          fprintf(CNF, ">= %d;\n", lclause_size_pb_comp[i]-1);
        }
      }
      else if (gcmd_line.makeISCAS == 1) {

        int* vec_vars;
        vec_vars = (int*)malloc((code) * sizeof(int));
        memset(vec_vars, 0, (code));

        for (i = 0; i < lnum_clauses; i++) {
          for (j = 0; j < lclause_size[i]; j++) {
            if (lclause[i][j] < 0)
              vec_vars[-1*lclause[i][j]] = 1;
            else
              vec_vars[lclause[i][j]] = 1;
          }
        }

        for (i=0; i<code; i++) {
          if (vec_vars[i]) {
            fprintf(CNF, "INPUT(V%d)\n", i);	
          }
        }
        for (i=0; i<code; i++) {
          if (vec_vars[i]) {
            fprintf(CNF, "NV%d=NOT(V%d)\n", i, i);	
          }
        }
        for (i = 0; i < lnum_clauses; i++) {
          if (lclause_size[i]==1) {
            if (lclause[i][0]<0) {
              fprintf(CNF, "CL%d=BUFF(NV%d)\n", i, -1*lclause[i][0]);	
            }
            else {
              fprintf(CNF, "CL%d=BUFF(V%d)\n", i, lclause[i][0]);	
            }
          }
          else {
            fprintf(CNF, "CL%d=OR(", i);	
            for (j = 0; j < lclause_size[i]; j++) {
              if (lclause[i][j] < 0)
                fprintf(CNF, "NV%d", -1*lclause[i][j]);
              else
                fprintf(CNF, "V%d", lclause[i][j]);
              if (j != lclause_size[i] - 1)
                fprintf(CNF, ", ");
            }
            fprintf(CNF, ")\n");
          }
        }
        fprintf(CNF, "RES=AND(");	
        for (i = 0; i < lnum_clauses; i++) {
          fprintf(CNF, "CL%d", i);
          if (i != lnum_clauses - 1)
            fprintf(CNF, ", ");
        }
        fprintf(CNF, ")\n");
        fprintf(CNF, "OUTPUT(RES)\n");
      }
      else {

        printf(
            "\n\nDECISION LAYER %d, WRITING THIN GP-BASED ENCODING WITH %d VARS, %d CLAUSES.\n",
            layer, code - 1, lnum_clauses);

        fprintf(CNF,
            "c CNF file planning task -p %s, -o %s, -f %s, bound %d, thin gp-based encoding\n",
            gcmd_line.path, gcmd_line.ops_file_name,
            gcmd_line.fct_file_name, layer);

        fprintf(CNF, "p cnf %d %d\n", code - 1, lnum_clauses);
        for (i = 0; i < lnum_clauses; i++) {
          for (j = 0; j < lclause_size[i]; j++) {
            fprintf(CNF, "%d ", lclause[i][j]);
          }
          fprintf(CNF, "0\n");
        }
      }




      fclose(CNF);

      /* Razer - generate prefs */
      if (gcmd_line.makePREFS == 1) {
        /* the first variable or 2 CNF POSITIVE is generated as prefs.txt */
        FILE *prefs;

        if ((prefs = fopen("prefs.txt", "w")) == NULL ) {
          printf("\n\ncan't open PREFS file.\n\n");
          exit(1);
        }

        i = 0;
        for (i=0; i<code; i++) {
          if (vec_2cnf[i]) {
            fprintf(prefs, "%d\n", i);
          }
        }

        fclose(prefs);

      }

      FILE *LITS;
      if ((LITS = fopen("lits.txt", "w")) == NULL ) {
        printf("\n\nEXIT: can't open LITS file.\n\n");

      }
      else {
        for (i=1; i<=code; i++) {
          /* operador */
          int oper = lop_to_code[i];
          if (oper != 0) {
            /*					fprintf(LITS, "%d - %s - OPER\n", i, goperators[gop_conn[oper].op]->name); */
            fprintf(LITS, "%d - OPER\n", i);
          }
          else {
            /* fato */
            /* fprintf(LITS, "%s - FACT\n", goperators[gop_conn[fop_to_code[i]].op]->name); */
          }
        }
        fclose(LITS);
      }
    }

  }
}
