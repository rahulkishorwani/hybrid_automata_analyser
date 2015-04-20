//============================================================================
// Name        : mtp_proj.cpp
// Author      : 
// Version     :
// Copyright   : Your copyright notice
// Description : Hello World in C++, Ansi-style
//============================================================================

#include "mtp_proj.h"


using namespace std;
using namespace Parma_Polyhedra_Library;
using namespace Parma_Polyhedra_Library::IO_Operators;



int main() {

	Automaton_List aut_lst;
	string s;
	ifstream r;
	//r.open("composition_demo.pha");
	//r.open("gas_burner.pha");
	//r.open("water_level_monitor.pha");
	//r.open("compo.pha");
	r.open("new_compo.pha");


	parseFile(r,aut_lst);


	aut_lst.fill_Regions();

	aut_lst.fill_Maps();

	//cout<<"Before calling:"<<aut_lst.aut_arr.size()<<endl;





	vector<vector<State> > R_f,R_i;

	initialize_final_states(R_f,aut_lst);
	//initialize_initial_states(R_i,aut_lst);
	//cout<<"End1:"<<endl;
	Automaton prod_aut=take_product(aut_lst);
	//aut_lst.aut_arr.push_back(prod_aut);

	/*cout<<"Automaton Name:"<<prod_aut.name<<endl;
	cout<<"Control Variable List:";
	for(vector<string>::iterator sit=prod_aut.cntr_var_lst.cntr_var_arr.begin();sit!=prod_aut.cntr_var_lst.cntr_var_arr.end();sit++)
	{
		cout<<" "<<(*sit);
	}
	cout<<endl;

	cout<<"Synchronization Label:"<<endl;
	for(vector<Synchronizing_Label>::iterator it=prod_aut.syn_lab_lst.syn_lab_arr.begin();it!=prod_aut.syn_lab_lst.syn_lab_arr.end();it++)
	{
		cout<<" "<<it->name;
	}
	cout<<endl;

	cout<<"Parameters:"<<endl;
	for(vector<Parameter>::iterator it=prod_aut.parameter_lst.par_list_arr.begin();it!=prod_aut.parameter_lst.par_list_arr.end();it++)
	{
		cout<<" "<<it->name;
	}
	cout<<endl;
	cout<<"Initial Location:"<<endl;
	for(vector<Location>::iterator it=prod_aut.initial_loc_lst.location_arr.begin();it!=prod_aut.initial_loc_lst.location_arr.end();it++)
	{
		cout<<it->name<<","<<it->invariants<<endl;
	}*/
	cout<<"Location List:"<<endl;
	for(vector<Location>::iterator it=prod_aut.loc_lst.location_arr.begin();it!=prod_aut.loc_lst.location_arr.end();it++)
	{
		cout<<it->name<<","<<it->invariants<<","<<it->rate<<endl;
	}

	cout<<"Edge List:"<<endl;
	for(vector<Edge>::iterator it=prod_aut.edge_lst.edge_arr.begin();it!=prod_aut.edge_lst.edge_arr.end();it++)
	{
		cout<<" "<<it->pre<<" "<<it->post<<" "<<it->guards<<" "<<it->syn_lab<<endl;
	}
	cout<<"End2:"<<endl;

	//int p;
	//cin>>p;


	int max_iterations=12;


	//cout<<"Output1:"<<is_Reachable_by_backward_fixpoint_computation(R_f,R_i,max_iterations,aut_lst)<<endl;

	//cout<<"Output2:"<<is_Reachable_by_forward_fixpoint_computation(R_f,R_i,max_iterations,aut_lst)<<endl;




	return 0;
}


/*
int main() {

	Automaton_List aut_lst;
	string s;
	ifstream r;
	//r.open("composition_demo.pha");
	//r.open("gas_burner.pha");
	r.open("water_level_monitor.pha");
	parseFile(r,aut_lst);


	aut_lst.fill_Regions();

	aut_lst.fill_Maps();




	vector<vector<State> > R_f,R_i;

	initialize_final_states(R_f,aut_lst);
	initialize_initial_states(R_i,aut_lst);
	int max_iterations=12;


	//cout<<"Output1:"<<is_Reachable_by_backward_fixpoint_computation(R_f,R_i,max_iterations,aut_lst)<<endl;

	cout<<"Output2:"<<is_Reachable_by_forward_fixpoint_computation(R_f,R_i,max_iterations,aut_lst)<<endl;


	return 0;
}


*/

