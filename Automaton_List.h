#include <vector>

#include "Automaton.h"
using namespace std;


class Automaton_List
{
public:
	vector<Automaton> aut_arr;
	Input_Variable_List in_var_lst;
	void fill_Regions();
	void fill_Maps();
};
void Automaton_List ::fill_Regions()
{
	for(vector<Automaton>::iterator it=aut_arr.begin();it!=aut_arr.end();it++)
	{
		it->fillRegions();
	}
}
void Automaton_List:: fill_Maps()
{

	for(vector<Automaton>::iterator it=aut_arr.begin();it!=aut_arr.end();it++)
	{
		it->fillMaps();
	}
}
void find_Initial_Locations(vector<Location> &Riloc_queue,vector<vector<Location> > &initial_states,vector<Automaton>::iterator curr,vector<Automaton>::iterator ed)
{

	for(vector<Location>::iterator itt=curr->initial_loc_lst.location_arr.begin();itt!=curr->initial_loc_lst.location_arr.end();itt++)
	{
		Riloc_queue.push_back(*itt);

		if( (curr+1)==ed )
		{
			initial_states.push_back(Riloc_queue);
		}
		else
		{
			find_Initial_Locations(Riloc_queue,initial_states,curr+1,ed);
		}

		Riloc_queue.pop_back();
	}
}

Location convert_vector_loc_to_location_with_original_invariants(vector<Location> st,Automaton_List aut_lst)
{
	Location ret;
	ret.name="";
	for(vector<Location>::iterator it=st.begin();it!=st.end();it++)
	{
		if(it!=st.begin())
		{
			ret.name=ret.name+"~";
		}
		ret.name=ret.name+(*it).name;


		Location tmp;

		for(vector<Automaton>::iterator aut_it=aut_lst.aut_arr.begin();aut_it!=aut_lst.aut_arr.end();aut_it++)
		{
			if((*aut_it).loc_to_Location.find((*it).name)!=(*aut_it).loc_to_Location.end())
			{
				tmp=(*aut_it).loc_to_Location[(*it).name];
				break;
			}
		}

		ret.invariants=ret.invariants^tmp.invariants;

		ret.rate=ret.rate^tmp.rate;
	}
	return ret;
}


Location convert_vector_loc_to_location(vector<Location> st,Automaton_List aut_lst)
{
	Location ret;
	ret.name="";
	for(vector<Location>::iterator it=st.begin();it!=st.end();it++)
	{
		if(it!=st.begin())
		{
			ret.name=ret.name+"~";
		}
		ret.name=ret.name+(*it).name;

		ret.invariants=ret.invariants^(*it).invariants;

		ret.rate=ret.rate^(*it).rate;

	}
	return ret;
}
bool sort_by_aut_to_vector(pair<string,string> p1,pair<string,string> p2)
{
	return (p1.second.compare(p2.second)<0);
}


bool sort_by_aut(Edge e1,Edge e2)
{
	return (e1.aut_nm.compare(e2.aut_nm)<0);
}
void insert_Location_Into_Prod(Automaton &prod,vector<Location> post)
{
	Location l;

	l.name="";
	for(vector<Location>::iterator lit=post.begin();lit!=post.end();lit++)
	{
		if(lit!=post.begin())
		{
			l.name=l.name+"~";
		}
		l.name=l.name+(*lit).name;

		l.invariants=l.invariants^(*lit).invariants;

		l.rate=l.rate^(*lit).rate;

	}
	prod.loc_lst.location_arr.push_back(l);

}
Edge find_Edge(vector<Edge> el)
{
	Edge e;
	e.syn_lab=el.begin()->syn_lab;

	for(vector<Edge>::iterator eit=el.begin();eit!=el.end();eit++)
	{
		e.guards=e.guards^(*eit).guards;
		e.updates=e.updates^(*eit).updates;
	}
	return e;

}
void insert_Edge_List_Into_Prod(Automaton &prod,vector<vector<Edge> > el)
{

	//e.aut_nm
	//e.guards
	//e.post
	//e.pre
	//e.syn_lab
	//e.updates


	for(vector<vector<Edge> >::iterator veit=el.begin();veit!=el.end();veit++)
	{
		Edge e;
		e.aut_nm=prod.name;
		e.syn_lab=veit->begin()->syn_lab;

		for(vector<Edge>::iterator eit=veit->begin();eit!=veit->end();eit++)
		{
			if(eit!=veit->begin())
			{
				e.pre=e.pre+"~";
				e.post=e.post+"~";
			}
			e.pre=e.pre+(*eit).pre;
			e.post=e.post+(*eit).post;

			e.guards=e.guards^(*eit).guards;
			e.updates=e.updates^(*eit).updates;
		}
		prod.edge_lst.edge_arr.push_back(e);
	}

}
void findPostLocEdge(vector<Location>::iterator vlbegin,vector<Location>::iterator vlcurr,vector<Location>::iterator vlend,vector<vector<Location> > &llist,vector<vector<Edge> > &elist,vector<vector<Edge> > vvelist,vector<Location> &vl_stack,vector<Edge> &el_stack,Automaton_List aut_lst,Automaton &prod)
{
	//vector<Location>::iterator vlcurr
	//vector<Location>::iterator vlend
	//vector<vector<Location> > &llist
	//vector<vector<Edge> > &elist
	//vector<vector<Edge> > vvelist
	//vector<Location> &vl_stack
	//vector<Edge> &el_stack
	if(vlcurr==vlend)
	{

		llist.push_back(vl_stack);
		elist.push_back(el_stack);

		//insert_Edge_List_Into_Prod
		Edge e=find_Edge(el_stack);
		e.aut_nm=prod.name;
		e.pre="";
		for(vector<Location>::iterator vit=vlbegin;vit!=vlend;vit++)
		{
			if(vit!=vlbegin)
			{
				e.pre=e.pre+"~";
			}
			e.pre=e.pre+vit->name;
		}

		e.post="";

		for(vector<Location>::iterator vit=vl_stack.begin();vit!=vl_stack.end();vit++)
		{
			if(vit!=vl_stack.begin())
			{
				e.post=e.post+"~";
			}
			e.post=e.post+vit->name;
		}
		prod.edge_lst.edge_arr.push_back(e);
		//vl_stack.pop_back();
		//el_stack.pop_back();
		//cout<<"here now:"<<llist.size()<<" "<<elist.size()<<endl;
		return;
	}
	bool flg=false;
	//assuming vvelist is only list of single synchronization label & is sorted by automaton
	for(vector<vector<Edge> >::iterator veit=vvelist.begin();veit!=vvelist.end();veit++)
	{
		if(veit->begin()->pre.compare(vlcurr->name)==0)
		{

			for(vector<Edge>::iterator eit=veit->begin();eit!=veit->end();eit++)
			{

				//put post location into vl_stack
				for(vector<Automaton>::iterator aut_it=aut_lst.aut_arr.begin();aut_it!=aut_lst.aut_arr.end();aut_it++)
				{
					if(aut_it->name.compare(eit->aut_nm)==0)
					{
						//cout<<"Compared:"<<veit->begin()->pre<<" "<<vlcurr->name<<endl;
						vl_stack.push_back(aut_it->loc_to_Location[eit->post]);
						break;
					}
				}

				el_stack.push_back(*eit);
				findPostLocEdge(vlbegin,vlcurr+1,vlend,llist,elist,vvelist,vl_stack,el_stack,aut_lst,prod);

				vl_stack.pop_back();
				el_stack.pop_back();

			}
			flg=true;

		}
	}
	if(flg==false)
	{
		vl_stack.push_back(*vlcurr);
		findPostLocEdge(vlbegin,vlcurr+1,vlend,llist,elist,vvelist,vl_stack,el_stack,aut_lst,prod);
		vl_stack.pop_back();
	}

}
bool is_in_vector_vector_location(vector<Location> post,vector<vector<Location> > que)
{
	for(vector<vector<Location> >::iterator vvlit=que.begin();vvlit!=que.end();vvlit++)
	{
		bool val=true;
		vector<Location>::iterator postlit;
		postlit=post.begin();
		for(vector<Location>::iterator vlit=vvlit->begin();vlit!=vvlit->end();vlit++)
		{
			if(vlit->name.compare(postlit->name)!=0)
			{
				val=false;
				break;
			}
			postlit++;

		}
		if(val==true)
			return true;
	}
	return false;
}

void generate_LocList_EdgeList(vector<vector<Location> > &llist,vector<vector<Edge> > &elist,vector<vector<Edge> > vvelist,vector<Location> vl,Automaton_List aut_lst,Automaton &prod)
{
	vector<Location> vl_stack;
	vector<Edge> el_stack;
	findPostLocEdge(vl.begin(),vl.begin(),vl.end(),llist,elist,vvelist,vl_stack,el_stack,aut_lst,prod);
	//cout<<"LList:"<<llist.size()<<endl;
}

void calculate_States(Automaton_List aut_lst,Automaton &prod,multimap<string,string> synlab_to_aut_map)
{
	vector<vector<Location> > initial_states;
	vector<Location> Riloc_queue;
	find_Initial_Locations(Riloc_queue,initial_states,aut_lst.aut_arr.begin(),aut_lst.aut_arr.end());

	for(vector<vector<Location> >::iterator it=initial_states.begin();it!=initial_states.end();it++)
	{
		Location l=convert_vector_loc_to_location(*it,aut_lst);
		prod.initial_loc_lst.location_arr.push_back(l);
	}

	vector<vector<Location> > loc_under_process_que;
	vector<vector<Location> > loc_already_processed_que;
	cout<<"Size:"<<initial_states.size()<<endl;
	for(vector<vector<Location> >::iterator it=initial_states.begin();it!=initial_states.end();it++)
	{
		Location vl=convert_vector_loc_to_location_with_original_invariants(*it,aut_lst);
		prod.loc_lst.location_arr.push_back(vl);
		loc_under_process_que.push_back(*it);
	}




	while(!loc_under_process_que.empty())
	{
		vector<Location> vl;
		vl=loc_under_process_que.front();
		cout<<"Before erasing:"<<loc_under_process_que.size()<<endl;
		loc_under_process_que.erase(loc_under_process_que.begin());

		cout<<"After erasing:"<<loc_under_process_que.size()<<endl;

		loc_already_processed_que.push_back(vl);

		Edge_List elist;
		for(vector<Location>::iterator lit=vl.begin();lit!=vl.end();lit++)
		{
			cout<<"Here"<<endl;

			Automaton aut;
			for(vector<Automaton>::iterator aut_it=aut_lst.aut_arr.begin();aut_it!=aut_lst.aut_arr.end();aut_it++)
			{
				if((*aut_it).loc_to_Location.find((*lit).name)!=(*aut_it).loc_to_Location.end())
				{
					aut=(*aut_it);
					break;
				}
			}
			pair<multimap<string,LocEdge>::iterator,multimap<string,LocEdge>::iterator> mm_to_mm;
			mm_to_mm=aut.pre_to_edge_plus_post.equal_range((*lit).name);
			for(multimap<string,LocEdge>::iterator mer=mm_to_mm.first;mer!=mm_to_mm.second;mer++)
			{
				//Edge e;
				//e=(*mer).second.e;
				(*mer).second.e.aut_nm=aut.name;
				elist.edge_arr.push_back((*mer).second.e);
			}
		}


		vector<vector<Edge> > velist;
		velist=elist.aggregate_on_sync_lab();


		//for each active syn label on edge
		for(vector<vector<Edge> >::iterator veit=velist.begin();veit!=velist.end();veit++)
		{
			//veit synctoautmap
			vector<vector<Edge> > vvelist;
			Edge_List tmpedgelist;
			for(vector<Edge>::iterator eit=(*veit).begin();eit!=(*veit).end();eit++)
			{
				tmpedgelist.edge_arr.push_back(*eit);
			}


			vvelist=tmpedgelist.aggregate_on_aut();

			//cout<<"Number of edges:"<<vvelist.size()<<endl;


			pair<multimap<string,string>::iterator,multimap<string,string>::iterator> syn_aut;
			syn_aut=synlab_to_aut_map.equal_range(veit->begin()->syn_lab);
			cout<<"Current synlab:"<<veit->begin()->syn_lab<<endl;

			vector<pair<string,string> > vp;
			for(multimap<string,string>::iterator stst=syn_aut.first;stst!=syn_aut.second;stst++)
			{
				vp.push_back(pair<string,string>(stst->first,stst->second));
			}
			sort(vp.begin(),vp.end(),sort_by_aut_to_vector);
			//cout<<"Number of aut having "<<veit->begin()->syn_lab<<" as label "<<vp.size()<<endl;

			if(vp.begin()->first.compare("")!=0)
			{
				vector<pair<string,string> >::iterator vpit=vp.begin();
				vector<vector<Edge> >::iterator vvelistit=vvelist.begin();

				while(vpit!=vp.end() && vvelistit!=vvelist.end())
				{
					//cout<<"AL:"<<vpit->second<<" "<<vvelistit->begin()->aut_nm<<" "<<vpit->second.compare(vvelistit->begin()->aut_nm)<<endl;
					if(vpit->second.compare(vvelistit->begin()->aut_nm)==0)
					{
						//cout<<"Compared successfully "<<vpit->second<<" "<<vvelistit->begin()->aut_nm<<endl;
						vpit++;
						vvelistit++;


					}
					else
						break;
				}

				if(vpit==vp.end() && vvelistit==vvelist.end())
				{
					//cout<<"Hahaha"<<endl;
					//generate location and edge of resultant automata
					vector<vector<Location> > llist;
					vector<vector<Edge> > elist;
					generate_LocList_EdgeList(llist,elist,vvelist,vl,aut_lst,prod);

					cout<<"Location size:"<<llist.size()<<endl;
					for(vector<vector<Location> >::iterator postlit=llist.begin();postlit!=llist.end();postlit++)
					{
						//loc_already_processed_que (*postlit)
						//if(loc_already_processed_que.end()==find(loc_already_processed_que.begin(),loc_already_processed_que.end(),*postlit) && loc_under_process_que.end()==find(loc_under_process_que.begin(),loc_under_process_que.end(),*postlit))
						bool ans1=is_in_vector_vector_location(*postlit,loc_already_processed_que);
						bool ans2=is_in_vector_vector_location(*postlit,loc_under_process_que);
						if((!ans1) && (!ans2))
						{
							loc_under_process_que.push_back(*postlit);
							insert_Location_Into_Prod(prod,*postlit);
						}
					}


					//insert_Edge_List_Into_Prod(prod,elist);

					//if post location formed by it is already in the loc list of prod
						//add_this_aggregate edge to the edge of prod
					//else
						//add post location to loc list
						//add_this_aggregate edge to the edge of prod

				}
			}
			else
			{
				//generate location and edge of resultant automata
				//if post location formed by it is already in the loc list of prod
					//add_this_aggregate edge to the edge of prod
				//else
					//add post location to loc list
					//add_this_aggregate edge to the edge of prod

			}


			//if current set of edges have exactly same automatons
				//if post location formed by it is already in the loc list of prod
					//add_this_aggregate edge to the edge of prod
				//else
					//add post location to loc list
					//add_this_aggregate edge to the edge of prod
			//else
				//discard the edge


		}
	}
}

Automaton take_product(Automaton_List aut_lst)
{
	multimap<string,string> synlab_to_aut_map;
	Automaton prod;
	/*	Control_Variable_List cntr_var_lst;
		Parameter_List parameter_lst;
		Synchronizing_Label_List syn_lab_lst;
		Input_Variable_List in_var_lst;*/
	int var_no=0;
	string aut_nm;
	aut_nm="";
	for(vector<Automaton>::iterator aut_it=aut_lst.aut_arr.begin();aut_it!=aut_lst.aut_arr.end();aut_it++)
	{
		if(aut_it!=aut_lst.aut_arr.begin())
		{
			aut_nm=aut_nm+"~";
		}
		aut_nm=aut_nm+aut_it->name;
		for(vector<string>::iterator cntr_it=aut_it->cntr_var_lst.cntr_var_arr.begin();cntr_it!=aut_it->cntr_var_lst.cntr_var_arr.end();cntr_it++)
		{

			prod.cntr_var_lst.cntr_var_arr.push_back(*cntr_it);
			prod.cntr_var_lst.cntr_vars.push_back(Variable(var_no));
			var_no++;
		}
		for(vector<Parameter>::iterator par_it=aut_it->parameter_lst.par_list_arr.begin();par_it!=aut_it->parameter_lst.par_list_arr.end();par_it++)
		{
			if(prod.parameter_lst.par_list_arr.end()==find(prod.parameter_lst.par_list_arr.begin(),prod.parameter_lst.par_list_arr.end(),*par_it))
			{
				prod.parameter_lst.par_list_arr.push_back(*par_it);
			}
		}
		for(vector<Synchronizing_Label>::iterator syn_it=aut_it->syn_lab_lst.syn_lab_arr.begin();syn_it!=aut_it->syn_lab_lst.syn_lab_arr.end();syn_it++)
		{
			synlab_to_aut_map.insert(pair<string,string>(syn_it->name,aut_it->name));

			if(prod.syn_lab_lst.syn_lab_arr.end()==find(prod.syn_lab_lst.syn_lab_arr.begin(),prod.syn_lab_lst.syn_lab_arr.end(),*syn_it))
			{
				prod.syn_lab_lst.syn_lab_arr.push_back(*syn_it);
			}
		}


	}
	prod.assign_Name(aut_nm);
	//cout<<"Automaton name:"<<prod.name<<endl;

	calculate_States(aut_lst,prod,synlab_to_aut_map);

	return prod;
}
