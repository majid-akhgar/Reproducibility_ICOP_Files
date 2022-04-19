/* -*- mode: C++; indent-tabs-mode: nil; -*-
 *
 * This file is a part of LEMON, a generic C++ optimization library.
 *
 * Copyright (C) 2003-2013
 * Egervary Jeno Kombinatorikus Optimalizalasi Kutatocsoport
 * (Egervary Research Group on Combinatorial Optimization, EGRES).
 *
 * Permission to use, modify and distribute this software is granted
 * provided that this copyright notice appears in all copies. For
 * precise terms see the accompanying LICENSE file.
 *
 * This software is provided "AS IS" with no warranty of any kind,
 * express or implied, and with no claim as to its suitability for any
 * purpose.
 *
 */

#include <sstream>
#include <random>
#include <iostream>
#include <stdio.h>
#include <vector>
#include <iterator> 
#include <queue>
#include <list>
#include<cmath>
#include <numeric>
#include <algorithm>
#include <math.h>
#include <conio.h>
#include <functional>
#include <stdlib.h>      /*srand, rand*/
#include <time.h>        /*time*/
#include <stdlib.h>      /*abs*/
#include<string>
#include<fstream>
#include <lemon/smart_graph.h>
#include <lemon/adaptors.h>
#include <lemon/concepts/digraph.h>
#include <lemon/concepts/maps.h>
#include <lemon/lgf_reader.h>
#include <lemon/hao_orlin.h>
#include <lemon/min_cost_arborescence.h>
#include <ilcplex/ilocplex.h>
#define MAX_N 500000

#include "C:\Users\akhga\Downloads\lemon-main-4fd76139b69e\lemon-main-4fd76139b69e\test\test_tools.h" //Please change this link according to your local repositories for Lemon library!

using namespace lemon;
using namespace std;


//This function calculates the square of distance between two segments.
std::vector<std::vector<double> > loc;
double Fsqua(double tk, double tl, int i, int j)
{
	double F;
	double first = loc[i][1] + tk * (loc[i][3] - loc[i][1]) - (loc[j][1] + tl * (loc[j][3] - loc[j][1]));
	double second = loc[i][0] + tk * (loc[i][2] - loc[i][0]) - (loc[j][0] + tl * (loc[j][2] - loc[j][0]));
	F = first * first + second * second;

	return F;
}

//This function calculates the distance between two segments.
double seg_dist(double a, double b, double x, double y, double xx, double yy)
{
	double distance_0;
	double tstar = ((a - x) * (xx - x) + (b - y) * (yy - y)) / ((pow((x - xx), 2.0) + pow((y - yy), 2.0)));
	if (0.0 <= tstar && tstar <= 1.0) {
		distance_0 = sqrtf(pow((x + tstar * (xx - x) - a), 2.0) + pow((y + tstar * (yy - y) - b), 2.0));
	}
	if (tstar < 0.0) {
		distance_0 = sqrtf(pow((x - a), 2.0) + pow((y - b), 2.0));
	}
	if (tstar > 1.0) {
		distance_0 = sqrtf(pow((xx - a), 2.0) + pow((yy - b), 2.0));
	}

	return distance_0;
}


bool comp(double a, double b)
{
	return (a < b);
}

struct Node
{
	vector<int> adj;
};
Node matrix[MAX_N];

double round_to_dec(double a)
{
	a = std::ceil(a * 10000.0) / 10000.0;
	return a;
}

//Defining required parameters, sets, vectors, etc.
std::default_random_engine generator;
int a = 1, b = 10;
std::uniform_int_distribution<int> distribution(a, b);
typedef IloArray<IloBoolVarArray> BoolVarMatrix;
typedef IloArray<IloNumVarArray> NumVarMatrix;
typedef IloArray<NumVarMatrix>   NumVar3Matrix;
std::string lgf;
int N;
int N_f;
int N_arc;
int E;
double Gap;
double Zcheck;
double timelimit;
int iteration;
int mip_ite;
int usercut;
int cove;
double M_ite;
double LB_x = -96.9 * 10.0 / 0.3;
double UB_x = -96.6 * 10.0 / 0.3;
double LB_y = 32.6 * 10.0 / 0.3;
double UB_y = 32.9 * 10.0 / 0.3;
std::vector<double> al_1;
std::vector<double> al_2;
std::vector<double> q;
std::vector<vector<double>> Y;
std::vector<double> delta_k;
std::vector<vector<double>> delta_fk;
std::vector<double> d_lk;
std::vector<double> g_lk;
std::vector<double> e_lk;
std::vector<std::vector<int>> data1;
std::vector<int> temp;
std::vector<int> big_M;
std::vector<double> BigM(2, 0);
std::vector<double> feas_obj;




ILOLAZYCONSTRAINTCALLBACK7(Mycallback, NumVarMatrix, y_fk, IloNumVar, z, IloNumVarArray, eta_lk, IloNumVarArray, alpha_1, IloNumVarArray, alpha_2, NumVarMatrix, tSta_fk, IloConstraintArray, cutpool) {
	try {

		//To check first feasible solution of B&B
		if (getNnodes() == 0 && mip_ite == 0 && getIncumbentObjValue() > 0.0) {
			feas_obj.push_back(getIncumbentObjValue());
		}

		//Defining Lemon credentials
		typedef SmartDigraph graph;
		typedef graph::Node Node;
		typedef graph::Arc Arc;
		typedef graph::NodeIt NodeIt;
		typedef graph::ArcIt ArcIt;
		typedef graph::ArcMap<double> CostMap;
		graph g;
		CostMap cost(g);
		graph::ArcMap<double> cap(g); //used for Hao and Orlin Algo in while loop
		graph::NodeMap<bool> cut(g);   //used for identifying which node is in the cut
		ArcIt i(g);
		Node nd; //start node for min-cuts
		NodeIt j(g);

		//Pulling info about the feas solution.
		al_1.resize(N_f);
		al_2.resize(N_f);
		Zcheck = getObjValue();
		Y.resize(N_f, vector<double>(N));
		for (int k = 0; k < N; k++) {
			int violation = 0;
			for (int f = 0; f < N_f; f++) {
				Y[f][k] = getValue(y_fk[f][k]);
				al_1[f] = getValue(alpha_1[f]);
				al_2[f] = getValue(alpha_2[f]);
			}
		}
		e_lk.resize(N_arc, 0.0);
		for (int e = 0; e < N_arc; e++) {
			e_lk[e] = getValue(eta_lk[e]);
		}

		//Reading the input for Lemon
		istringstream input(lgf);
		digraphReader(g, input)
			.run();
		//Assigning the source node for solving min-cuts
		for (ArcIt i(g); i != INVALID; ++i) {
			nd = g.source(i);
		}

		//Calculating solution time for adding cuts
		time_t start3, end3;
		double total_time3;
		start3 = clock();

		//Hao and Orlin, capacity assigning
		int cou = N_arc;
		int cou_2 = N;

		for (ArcIt i(g); i != INVALID; ++i) {
			if (cou != 0) {
				cap[i] = d_lk[cou - 1] * e_lk[cou - 1] + g_lk[cou - 1];
				cou = cou - 1;
			}
			else
			{
				double su = 0;
				for (int f = 0; f < N_f; f++) {
					su += Y[f][cou_2 - 1];
				}
				cap[i] = delta_k[cou_2 - 1] * su;
				cou_2 = cou_2 - 1;
			}
		}


		{
			HaoOrlin<SmartDigraph> ho(g, cap);
			ho.init(nd);
			ho.calculateOut();
			ho.minCutMap(cut);
			Gap = abs(Zcheck - ho.minCutValue()) / ho.minCutValue();
			if (Gap >= 0.001) {
				std::vector<int> cut1(N, 1);
				int cou3 = N;
				for (NodeIt j(g); j != INVALID; ++j) {
					if (cut[j] == 0) {
						cut1[cou3 - 1] = 0;
					}
					cou3 = cou3 - 1;
				}

				//Adding new constraint
				IloExpr nc(getEnv());
				for (int k = 0; k < N; k++) {
					if (cut1[k] == 0) {
						IloExpr nsum1(getEnv());
						for (int f = 0; f < N_f; f++) {
							nsum1 += y_fk[f][k];
						}
						IloExpr nsum11(getEnv());
						for (std::vector <int>::iterator it = matrix[k + 1].adj.begin(); it != matrix[k + 1].adj.end(); it++) {
							nsum11 += cut1[data1[*it + (2 * N + 6)][0] - 1] * (d_lk[*it] * eta_lk[*it] + g_lk[*it]);
						}
						nc += delta_k[k] * nsum1 + nsum11;
					}

				}

				add(nc >= z);
				cutpool.add(nc >= z);
				nc.end();
				iteration += 1;
			}

		}
		end3 = clock();
		total_time3 = (double)(end3 - start3) / (double)CLK_TCK;
		timelimit += total_time3;
	}
	catch (IloException& e) {
		cerr << "Concert Exception in Callback: " << e << endl;
	}

	catch (...) {
		cerr << "Other Exception in Callback" << endl;
	}

}

int main(int argc, char* argv[]) {


	string instance = argv[1]; //Instance File Name

	//Input the number of node
	cout << "Enter the number of node";
	cin >> N;

	//Input the number of fences
	cout << "Enter the number of fences";
	cin >> N_f;

	//Input radii of fences
	q.resize(N_f);
	for (int r = 0; r < N_f; r++) {
		int radius;
		cout << "Enter radius";
		cin >> radius;
		q[r] = radius;
	}

	//Some general parameters, vectors, etc.
	Gap = 0;
	Zcheck = 0;
	timelimit = 0;
	iteration = 0;
	mip_ite = 0;
	M_ite = 0;
	std::vector<int> coverage(N_f, 0);
	int num_k = 0;
	int v = 0;
	double time = 0;
	int ave_ite = 0;
	double gap_ave = 0;
	//######################################

	do {

		//Running time for reading files and creating parameters
		time_t start, end;
		double total_time;
		start = clock();

		//Rreading data
		std::string str = "C:\\Users\\akhga\\source\\repos\\DitoLgf\\ICpaper\\" + instance; //PLease change the link according to repository you put the instance data. 
		std::ifstream file(str);
		if (!file) {
			std::cout << "Cannot open input file.\n" << endl;
			std::cin.get();
		}
		int ite = 0;
		std::string t;
		while (std::getline(file, t)) {
			std::istringstream in(t);
			std::copy(std::istream_iterator<int>(in), std::istream_iterator<int>(), std::back_inserter(temp));
			data1.push_back(temp);
			ite += 1;
			if (ite > 6 + 2 * N) {
				matrix[temp[1]].adj.push_back(ite - (2 * N + 7));

			}
			temp.clear();
		}

		//Reading locations file
		std::vector<double> temp1;
		std::string str1 = "C:\\Users\\akhga\\source\\repos\\DitoLgf\\ICpaper\\L2." + instance; //PLease change the link according to repository you put the location data.
		std::ifstream file1(str1);
		if (!file1) {
			std::cout << "Cannot open locations file.\n" << endl;
			std::cin.get();
		}
		std::string t1;
		while (std::getline(file1, t1)) {
			std::istringstream in(t1);
			std::copy(std::istream_iterator<double>(in), std::istream_iterator<double>(), std::back_inserter(temp1));
			loc.push_back(temp1);
			temp1.clear();
		}

		//Modifying the file specifically for Lemon
		std::ifstream file2(str);
		if (!file2) {
			std::cout << "Cannot open Lemon file.\n" << endl;
			std::cin.get();
		}
		std::string lgfCur;
		while (std::getline(file2, lgfCur)) {
			lgf += lgfCur;
			lgf += '\n';

		}


		N_arc = data1[0][1] - N; //Number of arcs
		E = data1[0][1]; //m+n

		//Generating parameters for influence constraints
		int k0 = log10(E);
		double k = pow(10, k0);
		double k_E = k / E;

		delta_k.resize(N, N);


		d_lk.resize(N_arc, N_arc);

		g_lk.resize(N_arc, 0);
		for (int i = 0; i < N_arc; i++) {
			g_lk[i] = round_to_dec(k_E * distribution(generator));
		}

		//Reading feasible solutions data
		std::string str2 = instance.erase(instance.length() - 4, instance.length()) + std::to_string(1) + ".txt";
		std::vector<vector<int>> indexes;
		std::vector<int> temp3;
		std::string str3 = "C:\\Users\\akhga\\source\\repos\\DitoLgf\\ICpaper\\Cov12." + instance + ".txt"; //Please change the link according to repository you put the coverage solution data.
		std::ifstream file3(str3);
		if (!file3) {
			std::cout << "Cannot open 1Fence file.\n" << endl;
			std::cin.get();
		}
		std::string t3;
		while (std::getline(file3, t3)) {
			std::istringstream in(t3);
			std::copy(std::istream_iterator<int>(in), std::istream_iterator<int>(), std::back_inserter(temp3));
			indexes.push_back(temp3);
			temp3.clear();
		}

		//Modifying g_lk
		std::vector<int> myset(indexes[0].size() + indexes[1].size(), 0);
		for (int i = 0; i < indexes[0].size(); i++) {
			myset[i] = indexes[0][i];
		}
		for (int i = 0; i < indexes[1].size(); i++) {
			myset[i + indexes[0].size()] = indexes[1][i];
		}

		vector<int>::iterator c;

		for (int k = 0; k < N; k++) {
			c = find(myset.begin(), myset.end(), k);
			if (c != myset.end())
				for (std::vector <int>::iterator it = matrix[k + 1].adj.begin(); it != matrix[k + 1].adj.end(); it++) {
					g_lk[*it] = matrix[k + 1].adj.size();
				}
			else {
				for (std::vector <int>::iterator it = matrix[k + 1].adj.begin(); it != matrix[k + 1].adj.end(); it++) {
					g_lk[*it] = 1 / matrix[k + 1].adj.size();
				}
			}
		}



		end = clock();
		total_time = (double)(end - start) / (double)CLK_TCK;

		//Calculating solution time
		time_t start1, end1;
		double total_time1;
		start1 = clock();


		{
			time_t start2, end2; //Calculating solution time first LP
			double total_time2;
			start2 = clock();

			//MIP formulation
			IloEnv env;
			try {

				IloModel model(env);
				//Variables
				IloNumVar z(env, -IloInfinity, IloInfinity, ILOFLOAT, "z");

				NumVarMatrix y_fk(env, N_f);
				for (int f = 0; f < N_f; f++) {
					y_fk[f] = IloNumVarArray(env, N);
					for (int k = 0; k < N; k++) {
						y_fk[f][k] = IloNumVar(env, 0.0, 1.0, ILOBOOL);

						//set the name of variable for exporting model
						std::string str = "Y_f " + std::to_string(f) + "k" + std::to_string(k);
						const char* cc = str.c_str();
						y_fk[f][k].setName(cc);
					}
				}

				IloNumVarArray alpha_1(env, N_f);
				for (int f = 0; f < N_f; f++) {
					alpha_1[f] = IloNumVar(env, LB_x, UB_x, ILOFLOAT);
				}
				alpha_1.setNames("alpha1");

				IloNumVarArray alpha_2(env, N_f);
				for (int f = 0; f < N_f; f++) {
					alpha_2[f] = IloNumVar(env, LB_y, UB_y, ILOFLOAT);
				}
				alpha_2.setNames("alpha2");

				NumVarMatrix tSta_fk(env, N_f);
				for (int f = 0; f < N_f; f++) {
					tSta_fk[f] = IloNumVarArray(env, N);
					for (int k = 0; k < N; k++) {
						tSta_fk[f][k] = IloNumVar(env, 0.0, 1.0, ILOFLOAT);

						//set the name of variable for exporting model
						std::string str = "tSta_f " + std::to_string(f) + "k" + std::to_string(k);
						const char* cc = str.c_str();
						tSta_fk[f][k].setName(cc);
					}
				}

				IloNumVarArray eta_lk(env, N_arc);
				for (int e = 0; e < N_arc; e++) {
					eta_lk[e] = IloNumVar(env, 0.0, IloInfinity, ILOFLOAT);
				}
				eta_lk.setNames("E");

				NumVar3Matrix u_fki(env, N_f);
				for (int f = 0; f < N_f; f++) {
					u_fki[f] = NumVarMatrix(env, N);
					for (int k = 0; k < N; k++) {
						u_fki[f][k] = IloNumVarArray(env, 2);
						for (int i = 0; i < 2; i++) {
							u_fki[f][k][i] = IloNumVar(env, -IloInfinity, IloInfinity, ILOFLOAT);

							//set the name of variable for exporting model
							std::string str = "U_f " + std::to_string(f) + "k" + std::to_string(k) + "i" + std::to_string(i);
							const char* cc = str.c_str();
							u_fki[f][k][i].setName(cc);
						}

					}
				}

				//Objective function
				model.add(IloMaximize(env, z));

				//Influence Constraints
				//S_0
				IloExpr con(env);
				for (int k = 0; k < N; k++) {
					IloExpr sum(env);
					for (int f = 0; f < N_f; f++) {
						sum += y_fk[f][k];
					}
					con += delta_k[k] * sum;
				}
				model.add(con >= z);
				con.end();

				//S_a
				for (int k = 0; k < N; k++) {
					IloExpr sum1(env);
					for (int f = 0; f < N_f; f++) {
						sum1 += y_fk[f][k];
					}
					IloExpr sum11(env);
					for (std::vector <int>::iterator it = matrix[k + 1].adj.begin(); it != matrix[k + 1].adj.end(); it++) {
						sum11 += d_lk[*it] * eta_lk[*it] + g_lk[*it];
					}
					model.add(delta_k[k] * sum1 + sum11 >= z);
				}

				//S_i
				for (int n = 0; n < N; n++) {
					IloExpr nc(env);
					for (int k = 0; k < N; k++) {
						if (k != n) {
							IloExpr nsum1(env);
							for (int f = 0; f < N_f; f++) {
								nsum1 += y_fk[f][k];
							}
							IloExpr nsum11(env);
							for (std::vector <int>::iterator it = matrix[k + 1].adj.begin(); it != matrix[k + 1].adj.end(); it++) {
								if (data1[*it + (2 * N + 6)][0] - 1 == n) {
									nsum11 += d_lk[*it] * eta_lk[*it] + g_lk[*it];
								}
							}
							nc += delta_k[k] * nsum1 + nsum11;
							nsum1.end();
							nsum11.end();
						}

					}
					model.add(nc >= z);
					nc.end();
				}

				//Budget constraint
				std::vector<int> C_eta(N_arc, 1);
				IloExpr Bu(env);
				for (int e = 0; e < N_arc; e++) {
					Bu += C_eta[e] * eta_lk[e];
				}
				model.add(Bu <= 1);
				Bu.end();

				//Rectangular inequalities
				vector<vector<double>> output;
				for (int k = 0; k < N; k++) {
					double dk = (pow((loc[k][3] - loc[k][1]), 2.0) + pow((loc[k][2] - loc[k][0]), 2.0));
					for (int f = 0; f < N_f; f++) {
						//##### Parameters for Rec Constraints #####
						double r1 = round_to_dec(loc[k][1] - (q[f] / sqrtf(dk)) * (loc[k][3] - loc[k][1]));
						double r2 = round_to_dec(loc[k][0] - (q[f] / sqrtf(dk)) * (loc[k][2] - loc[k][0]));
						double rB1 = round_to_dec(loc[k][1] + (1 + (q[f] / sqrtf(dk))) * (loc[k][3] - loc[k][1]));
						double rB2 = round_to_dec(loc[k][0] + (1 + (q[f] / sqrtf(dk))) * (loc[k][2] - loc[k][0]));
						double rdk = round_to_dec(pow((rB1 - r1), 2.0) + pow((rB2 - r2), 2.0));

						double A1 = round_to_dec(r2 - loc[k][0] + r1);
						double A2 = round_to_dec(loc[k][1] - r1 + r2);
						double B1 = round_to_dec(loc[k][0] - r2 + r1);
						double B2 = round_to_dec(r1 - loc[k][1] + r2);
						double dAB = round_to_dec(pow((B1 - A1), 2.0) + pow((B2 - A2), 2.0));
						//##### Computing smallest and largest  t for Rec constraints
						double st;
						double lt;
						double st_AB;
						double lt_AB;
						double sst;
						double llt;
						double sst_AB;
						double llt_AB;

						if (loc[k][3] - loc[k][1] == 0.0) {

							st = round_to_dec(min({ (UB_y - r2) / (rB2 - r2) ,(LB_y - r2) / (rB2 - r2) }, comp));
							lt = round_to_dec(max({ (UB_y - r2) / (rB2 - r2) ,(LB_y - r2) / (rB2 - r2) }, comp));
							sst = min({ st,1 - lt }, comp);
							llt = max({ lt,1 - st }, comp);
							st_AB = round_to_dec(min({ (LB_x - A1) / (B1 - A1),(UB_x - A1) / (B1 - A1) }, comp));
							lt_AB = round_to_dec(max({ (LB_x - A1) / (B1 - A1),(UB_x - A1) / (B1 - A1) }, comp));
							sst_AB = min({ st_AB,1 - lt_AB }, comp);
							llt_AB = max({ lt_AB,1 - st_AB }, comp);


						}
						else {
							st = round_to_dec(min({ (LB_x - r1) / (rB1 - r1),(UB_x - r1) / (rB1 - r1) }, comp));
							lt = round_to_dec(max({ (LB_x - r1) / (rB1 - r1),(UB_x - r1) / (rB1 - r1) }, comp));
							sst = min({ st,1 - lt }, comp);
							llt = max({ lt,1 - st }, comp);
							st_AB = round_to_dec(min({ (UB_y - A2) / (B2 - A2), (LB_y - A2) / (B2 - A2) }, comp));
							lt_AB = round_to_dec(max({ (UB_y - A2) / (B2 - A2), (LB_y - A2) / (B2 - A2) }, comp));
							sst_AB = min({ st_AB,1 - lt_AB }, comp);
							llt_AB = max({ lt_AB,1 - st_AB }, comp);
						}
						//Rectangular inequalities
						model.add(0 <= ((alpha_1[f] - r1) * round_to_dec((rB1 - r1) / ((rB1 - r1) * (rB1 - r1) + (rB2 - r2) * (rB2 - r2))) + (alpha_2[f] - r2) * round_to_dec((rB2 - r2) / ((rB1 - r1) * (rB1 - r1) + (rB2 - r2) * (rB2 - r2)))) - sst * (1 - y_fk[f][k]));
						model.add(((alpha_1[f] - r1) * round_to_dec((rB1 - r1) / ((rB1 - r1) * (rB1 - r1) + (rB2 - r2) * (rB2 - r2))) + (alpha_2[f] - r2) * round_to_dec((rB2 - r2) / ((rB1 - r1) * (rB1 - r1) + (rB2 - r2) * (rB2 - r2)))) <= 1 + llt * (1 - y_fk[f][k]));

						model.add(0 <= ((alpha_1[f] - A1) * round_to_dec((B1 - A1) / ((B1 - A1) * (B1 - A1) + (B2 - A2) * (B2 - A2))) + (alpha_2[f] - A2) * round_to_dec((B2 - A2) / ((B1 - A1) * (B1 - A1) + (B2 - A2) * (B2 - A2)))) - sst_AB * (1 - y_fk[f][k]));
						model.add(((alpha_1[f] - A1) * round_to_dec((B1 - A1) / ((B1 - A1) * (B1 - A1) + (B2 - A2) * (B2 - A2))) + (alpha_2[f] - A2) * round_to_dec((B2 - A2) / ((B1 - A1) * (B1 - A1) + (B2 - A2) * (B2 - A2)))) <= 1 + llt_AB * (1 - y_fk[f][k]));
					}
				}

				//Conflict constraints 
				for (int i = 0; i < N; i++) {
					for (int j = i + 1; j < N; j++) {

						double a = -2 * (pow((loc[i][3] - loc[i][1]), 2.0) + pow((loc[i][2] - loc[i][0]), 2.0));
						double b = 2 * ((loc[i][3] - loc[i][1]) * (loc[j][3] - loc[j][1]) + (loc[i][2] - loc[i][0]) * (loc[j][2] - loc[j][0]));
						double c = 2 * ((loc[i][3] - loc[i][1]) * (loc[i][1] - loc[j][1]) + (loc[i][2] - loc[i][0]) * (loc[i][0] - loc[j][0]));
						double b2 = 2 * (pow((loc[j][3] - loc[j][1]), 2.0) + pow((loc[j][2] - loc[j][0]), 2.0));
						double c2 = 2 * ((loc[j][3] - loc[j][1]) * (loc[i][1] - loc[j][1]) + (loc[j][2] - loc[j][0]) * (loc[i][0] - loc[j][0]));
						double tl = (c * b + c2 * a) / (b * b + b2 * a);
						double tk = (b2 / b) * tl - (c2 / b);
						double disSta;
						if (0.0 <= tl & tl <= 1.0 & 0.0 <= tk & tk <= 1.0) {
							disSta = sqrtf(Fsqua(tk, tl, i, j));
						}
						else {
							double dist4 = 50;
							double dist5 = 50;
							double dist6 = 50;
							double dist7 = 50;
							double dist0 = sqrtf(Fsqua(0.0, 1.0, i, j));
							double dist1 = sqrtf(Fsqua(0.0, 0.0, i, j));
							double dist2 = sqrtf(Fsqua(1.0, 0.0, i, j));
							double dist3 = sqrtf(Fsqua(1.0, 1.0, i, j));
							if (tl < 0.0 & (c / a) <= 1.0 & 0.0 <= (c / a)) {
								dist4 = sqrtf(Fsqua(c / a, 0.0, i, j));
							}
							if (tk < 0.0 & (c2 / b2) <= 1.0 & 0.0 <= (c2 / b2)) {
								dist5 = sqrtf(Fsqua(0.0, c2 / b2, i, j));
							}
							if (tl > 1.0 & ((c - b) / a) <= 1.0 & 0.0 <= ((c - b) / a)) {
								dist6 = sqrtf(Fsqua((c - b) / a, 1.0, i, j));
							}
							if (tk > 1.0 & ((c2 + b) / b2) <= 1.0 & 0.0 <= ((c2 + b) / b2)) {
								dist7 = sqrtf(Fsqua(1.0, (c2 + b) / b2, i, j));
							}
							disSta = min({ dist0,dist1,dist2,dist3,dist4,dist5,dist6,dist7 }, comp);
						}
						for (int f = 0; f < N_f; f++) {
							if (disSta > 2 * q[f]) {
								model.add(y_fk[f][i] + y_fk[f][j] <= 1);
							}
						}
					}
				}

				IloConstraintArray cutpool(env); //To save lazy cuts

				//Solving MIP
				IloCplex solver(model);
				solver.setParam(IloCplex::Param::TimeLimit, 3600);

				IloNumVarArray Start_v(env);
				for (int f = 0; f < N_f; f++) {
					for (int k = 0; k < N; k++) {
						Start_v.add(y_fk[f][k]);
					}
				}

				IloNumArray Start_val(env);
				for (int f = 0; f < N_f; f++) {
					for (int k = 0; k < N; k++) {
						Start_val.add(0);
					}
				}
				for (int k = 0; k < indexes[0].size(); k++) {
					Start_val[indexes[0][k]] = 1;
				}
				for (int k = 0; k < indexes[1].size(); k++) {
					Start_val[N + indexes[1][k]] = 1;
				}

				solver.addMIPStart(Start_v, Start_val, IloCplex::MIPStartEffort::MIPStartRepair);

				//Callback
				IloCplex::Callback mycall = solver.use(Mycallback(env, y_fk, z, eta_lk, alpha_1, alpha_2, tSta_fk, cutpool));
				solver.solve();
				cout << solver.getStatus() << endl;
				Zcheck = solver.getObjValue();

				cout << "Master objective is" << Zcheck << endl;

				end2 = clock();
				total_time2 = (double)(end2 - start2) / (double)CLK_TCK;

				al_1.resize(N_f);
				al_2.resize(N_f);
				for (int f = 0; f < N_f; f++) {
					al_1[f] = solver.getValue(alpha_1[f]);
					al_2[f] = solver.getValue(alpha_2[f]);
					cout << "facility " << f << " has:( " << al_1[f] << " , " << al_2[f] << " ) as ccordinates" << " and q=" << q[f] << ". It covers following nodes: " << endl;
					int coun = 0;
					for (int k = 0; k < N; k++) {
						Y[f][k] = solver.getValue(y_fk[f][k]);
						if (Y[f][k] > 0.5) {
							coun = coun + 1;
							cout << k << ", ";
						}

					}
					cout << "Total Coverage is: " << coun << endl;
					coverage[f] = coun;
				}

				usercut += solver.getNcuts(IloCplex::CutType::CutUser);
				solver.exportModel("model0.lp");   //Verification of model

				if (total_time2 <= 3600) {
					int flag = 0;
					for (int k = 0; k < N; k++) {
						int condition = 0;
						for (int f = 0; f < N_f; f++) {
							if (Y[f][k] > 0.5) {
								double distance_0;
								distance_0 = seg_dist(al_1[f], al_2[f], loc[k][1], loc[k][0], loc[k][3], loc[k][2]);
								if (distance_0 > q[f] + 1e-3) {
									cout << "distance is " << distance_0 << " and " << k << " is violated" << endl;
									condition = condition + 1;
								}
							}
						}
						if (condition > 0 && mip_ite == 0) {
							//###Big M, for reformulation of the quadratic big_M
							double x1 = abs(UB_x - loc[k][1]);
							double x2 = abs(LB_x - loc[k][1]);
							double x3 = abs(UB_x - loc[k][3]);
							double x4 = abs(LB_x - loc[k][3]);
							BigM[0] = max({ x1,x2,x3,x4 }, comp);
							double y1 = abs(UB_y - loc[k][0]);
							double y2 = abs(LB_y - loc[k][0]);
							double y3 = abs(UB_y - loc[k][2]);
							double y4 = abs(LB_y - loc[k][2]);
							BigM[1] = max({ y1,y2,y3,y4 }, comp);

							for (int f = 0; f < N_f; f++) {

								//#Linear Big-M
								model.add(u_fki[f][k][0] * u_fki[f][k][0] + u_fki[f][k][1] * u_fki[f][k][1] <= q[f] * q[f]);
								model.add(u_fki[f][k][0] <= loc[k][1] + tSta_fk[f][k] * (loc[k][3] - loc[k][1]) - alpha_1[f] + BigM[0] * (1 - y_fk[f][k]));
								model.add(u_fki[f][k][1] <= loc[k][0] + tSta_fk[f][k] * (loc[k][2] - loc[k][0]) - alpha_2[f] + BigM[1] * (1 - y_fk[f][k]));
								model.add(u_fki[f][k][0] >= loc[k][1] + tSta_fk[f][k] * (loc[k][3] - loc[k][1]) - alpha_1[f] - BigM[0] * (1 - y_fk[f][k]));
								model.add(u_fki[f][k][1] >= loc[k][0] + tSta_fk[f][k] * (loc[k][2] - loc[k][0]) - alpha_2[f] - BigM[1] * (1 - y_fk[f][k]));

								M_ite = M_ite + 1;
								flag = flag + 1;
								big_M.push_back(k);
							}
						}

						if (condition > 0 && mip_ite > 0 && std::count(big_M.begin(), big_M.end(), k) == 0) {
							//###Big M, for reformulation of the quadratic big_M
							double x1 = abs(UB_x - loc[k][1]);
							double x2 = abs(LB_x - loc[k][1]);
							double x3 = abs(UB_x - loc[k][3]);
							double x4 = abs(LB_x - loc[k][3]);
							BigM[0] = max({ x1,x2,x3,x4 }, comp);
							double y1 = abs(UB_y - loc[k][0]);
							double y2 = abs(LB_y - loc[k][0]);
							double y3 = abs(UB_y - loc[k][2]);
							double y4 = abs(LB_y - loc[k][2]);
							BigM[1] = max({ y1,y2,y3,y4 }, comp);

							for (int f = 0; f < N_f; f++) {
								model.add(u_fki[f][k][0] * u_fki[f][k][0] + u_fki[f][k][1] * u_fki[f][k][1] <= q[f] * q[f]);
								model.add(u_fki[f][k][0] <= loc[k][1] + tSta_fk[f][k] * (loc[k][3] - loc[k][1]) - alpha_1[f] + BigM[0] * (1 - y_fk[f][k]));
								model.add(u_fki[f][k][1] <= loc[k][0] + tSta_fk[f][k] * (loc[k][2] - loc[k][0]) - alpha_2[f] + BigM[1] * (1 - y_fk[f][k]));
								model.add(u_fki[f][k][0] >= loc[k][1] + tSta_fk[f][k] * (loc[k][3] - loc[k][1]) - alpha_1[f] - BigM[0] * (1 - y_fk[f][k]));
								model.add(u_fki[f][k][1] >= loc[k][0] + tSta_fk[f][k] * (loc[k][2] - loc[k][0]) - alpha_2[f] - BigM[1] * (1 - y_fk[f][k]));

								M_ite = M_ite + 1;
								flag = flag + 1;
								big_M.push_back(k);
							}
						}
					}

					if (flag == 0) {
						break;
					}

					else {
						model.add(cutpool);
						model.add(z <= Zcheck);
						mip_ite = mip_ite + 1;
					}

					solver.exportModel("model.lp");   //Verification code
					solver.setParam(IloCplex::Param::TimeLimit, 3600 - total_time2);
					solver.solve();
					cout << solver.getStatus() << endl;
					Zcheck = solver.getObjValue();

					cout << "New Objective is" << Zcheck << endl;

					for (int f = 0; f < N_f; f++) {
						al_1[f] = solver.getValue(alpha_1[f]);
						al_2[f] = solver.getValue(alpha_2[f]);
						cout << "facility " << f << " has:( " << al_1[f] << " , " << al_2[f] << " )" << " and q=" << q[f] << ". It covers following nodes: " << endl;
						cove = 0;
						for (int k = 0; k < N; k++) {
							Y[f][k] = solver.getValue(y_fk[f][k]);
							if (Y[f][k] > 0.5) {
								cout << k << ", ";
								cove = cove + 1;
							}
						}
						cout << "Total Coverage is: " << cove << endl;
						coverage[f] = cove;
					}
					usercut += solver.getNcuts(IloCplex::CutType::CutUser);
				}
				cout << "Final Objective value is :" << Zcheck << endl;
				gap_ave += Gap;
			}

			catch (IloException& e) {
				cerr << "Concert Exception: " << e << endl;
			}

			catch (...) {
				cerr << "Other Exception" << endl;
			}
			env.end();
			cout << endl << endl;
		}

		end1 = clock();
		total_time1 = (double)(end1 - start1) / (double)CLK_TCK;
		v = v + 1;
		ave_ite += iteration;
		time += total_time1;
	} while (v != 1);

	cout << "Average solution time for " << instance << " is " << time / 1 << endl;;
	cout << "Average number of cuts for " << instance << " is " << ave_ite / 1 << endl;
	cout << "Average number of M for " << instance << " is " << M_ite / 1 << endl;
	cout << "Average optimality Gap for " << instance << " is " << gap_ave / 1 << endl;

	fstream save;
	save.open("ICOP.csv", ios::app);

	save << instance << " , " << Zcheck << " , " << *min_element(feas_obj.begin(), feas_obj.end()) << endl;


	return 0;

}