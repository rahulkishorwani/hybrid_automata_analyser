



vector<vector<State> > pre(vector<vector<State> > &R_cur,Automaton_List &a_lst)
{


	vector<vector<State> > rt;



	for(vector<vector<State> >::iterator itr=R_cur.begin();itr!=R_cur.end();itr++)
	{

		vector<State> ret;
		for(vector<State>::iterator it=(*itr).begin();it!=(*itr).end();it++)
		{
			for(vector<Automaton>::iterator itt=a_lst.aut_arr.begin();itt!=a_lst.aut_arr.end();itt++)
			{

				pair<multimap<string,LocEdge>::iterator,multimap<string,LocEdge>::iterator> mm_to_mm;
				mm_to_mm=(*itt).post_to_edge_plus_pre.equal_range((*it).l.name);


				for(multimap<string,LocEdge>::iterator mer=mm_to_mm.first;mer!=mm_to_mm.second;mer++)
				{

					Edge *ittt;
					ittt=&(*mer).second.e;

					//cout<<"Found "<<(*it).l.name<<" with guards "<<(*ittt).guards<<endl;


					State tmpstate;
					Location tmploc;
					NNC_Polyhedron tmp_poly;
					tmp_poly.add_space_dimensions_and_embed(a_lst.aut_arr.begin()->cntr_var_lst.cntr_var_arr.size());
					tmp_poly=(*it).poly;
					//add_trivial_constraints_to_poly(tmp_poly);
					cout<<"tmppoly:"<<tmp_poly<<endl;


					tmploc=(*itt).loc_to_Location[(*it).l.name];
					//cout<<tmploc.name<<" found"<<endl;



					NNC_Polyhedron invar;
					invar.add_space_dimensions_and_embed(a_lst.aut_arr.begin()->cntr_var_lst.cntr_var_arr.size());
					invar=invar^tmploc.invariants;
					//invar.add_constraints(tmploc.invariants);

					//add_trivial_constraints_to_poly(invar);
					//cout<<"Invariant:"<<invar<<endl;


					//add_trivial_constraints_to_poly((*it).poly);


					(*it).poly=(*it).poly^invar;
					//if(invar.contains((*it).poly))
					//{


						//take time elapse by negative rate
						NNC_Polyhedron rate_poly;
						rate_poly.add_space_dimensions_and_embed(a_lst.aut_arr.begin()->cntr_var_lst.cntr_var_arr.size());


						//cout<<"Rate:"<<tmploc.rate<<endl;
						//rate_poly.add_constraints(invert_Coefficients(tmploc.rate));
						rate_poly=rate_poly^invert_Coefficients(tmploc.rate);
						//cout<<"Rate poly:"<<rate_poly<<endl;



						tmp_poly=(*it).poly;
						//cout<<"tmp_poly:"<<(*it).poly<<endl;
						//cout<<"Rate poly:"<<rate_poly<<endl;
						tmp_poly.time_elapse_assign(rate_poly);
						cout<<"After 0st time elapse:"<<tmp_poly<<endl;
						//cout<<"After post location time elapse:"<<tmp_poly<<endl;

						add_trivial_constraints_to_poly(tmp_poly);

						cout<<"After post location time elapse:"<<tmp_poly<<endl;





						//take anding of this with invariant of this location
						tmp_poly.intersection_assign(invar);
						add_trivial_constraints_to_poly(tmp_poly);
						cout<<"After intersecting with invariants of post location:"<<tmp_poly<<endl;

						//replace updation vector of the edge in the representation of polyhedron


						if(tmp_poly.is_empty())
						{
								cout<<"Got empty polytope after updates are performed:"<<endl;
								//action has to be taken

						}




						//transform tmp_poly's constraint_system with updates i.e. replace for every occurence of left with right
						NNC_Polyhedron ttpoly;
						ttpoly.add_space_dimensions_and_embed(tmp_poly.space_dimension());
						ttpoly=tmp_poly;
						//ttpoly.add_constraints((*ittt).updates);
						ttpoly=ttpoly^(*ittt).updates;


						if(!ttpoly.is_empty())
						{
							cout<<"Polygon contains updates"<<endl;
						}
						else
							cout<<"Polygon does not contain updates"<<endl;

						//tmp_poly.add_constraints((*ittt).updates);

						tmp_poly=tmp_poly^(*ittt).updates;

						tmp_poly=apply_Updates(tmp_poly,(*ittt).updates);
						add_trivial_constraints_to_poly(tmp_poly);



						cout<<"After applying updates:"<<tmp_poly<<endl;
						//cout<<"Updates:"<<(*ittt).updates<<endl;









						//cout<<"After adding updates:"<<tmp_poly<<endl;






						//take anding of this with the guards of selected edge

						cout<<"Guards:"<<(*ittt).guards<<endl;
						//tmp_poly.add_constraints((*ittt).guards);
						tmp_poly=tmp_poly^(*ittt).guards;
						add_trivial_constraints_to_poly(tmp_poly);

						cout<<"After applying guards:"<<tmp_poly<<endl;

						//int idd;
						//scanf("%d",&idd);



						//time elapse with rate of pre location take anding of this with the invariant of the pre location

						map<string,Location>::iterator itk=(*itt).loc_to_Location.find((*ittt).pre);
						if(itk!=(*itt).loc_to_Location.end())
						{

							Location *locit;
							locit=&(*itk).second;
							//tmp_poly.add_constraints((*locit).invariants);
							tmp_poly=tmp_poly^(*locit).invariants;
							add_trivial_constraints_to_poly(tmp_poly);
							cout<<"After checking invariants of the pre location:"<<tmp_poly<<endl;

							//evolve with the time elapse relation of pre

							NNC_Polyhedron rate_poly1;
							rate_poly1.add_space_dimensions_and_embed(a_lst.aut_arr.begin()->cntr_var_lst.cntr_var_arr.size());
							//cout<<"Rate:"<<tmploc.rate<<endl;
							//rate_poly1.add_constraints(invert_Coefficients((*locit).rate));
							rate_poly1=rate_poly1^invert_Coefficients((*locit).rate);
							//cout<<"Rate poly:"<<rate_poly<<endl;
							tmp_poly.time_elapse_assign(rate_poly1);
							add_trivial_constraints_to_poly(tmp_poly);

							cout<<"After pre time elapse:"<<tmp_poly<<endl;



							//again take anding with invariants
							//tmp_poly.add_constraints((*locit).invariants);
							tmp_poly=tmp_poly^(*locit).invariants;
							add_trivial_constraints_to_poly(tmp_poly);

							cout<<"After checking invariants of pre location:"<<tmp_poly<<endl;

							tmpstate.l=(*locit);


						}

						//push back this state to the returning state vector
						tmpstate.poly=tmp_poly;
						add_trivial_constraints_to_poly(tmpstate.poly);
						//cout<<"Output:"<<tmp_poly<<endl;
						if(!tmp_poly.is_empty())
						{
							//cout<<"Here:"<<tmp_poly<<endl;
							ret.push_back(tmpstate);
						}
					//}
					//else
					//{
					//	cout<<"Invariant doesn't carry poly:"<<invar<<endl;
					//}

				}


			}

		}
		rt.push_back(ret);
	}
	cout<<"End of pre:"<<endl<<endl;
	return rt;


}



vector<vector<State> > post(vector<vector<State> > &R_cur,Automaton_List &a_lst)
{

	vector<vector<State> > rt;



	for(vector<vector<State> >::iterator itr=R_cur.begin();itr!=R_cur.end();itr++)
	{

		vector<State> ret;
		for(vector<State>::iterator it=(*itr).begin();it!=(*itr).end();it++)
		{
			for(vector<Automaton>::iterator itt=a_lst.aut_arr.begin();itt!=a_lst.aut_arr.end();itt++)
			{

				pair<multimap<string,LocEdge>::iterator,multimap<string,LocEdge>::iterator> mm_to_mm;
				mm_to_mm=(*itt).pre_to_edge_plus_post.equal_range((*it).l.name);
				for(multimap<string,LocEdge>::iterator mer=mm_to_mm.first;mer!=mm_to_mm.second;mer++)
				{
					Edge *ittt;
					ittt=&(*mer).second.e;

					//cout<<"Found "<<(*it).l.name<<" with guards "<<(*ittt).guards<<endl;

					//cout<<"post find out:"<<endl;
					State tmpstate;
					Location tmploc;
					NNC_Polyhedron tmp_poly;
					tmp_poly.add_space_dimensions_and_embed(a_lst.aut_arr.begin()->cntr_var_lst.cntr_var_arr.size());
					tmp_poly=(*it).poly;
					//add_trivial_constraints_to_poly(tmp_poly);
					cout<<"tmppoly:"<<tmp_poly<<endl;



					tmploc=(*itt).loc_to_Location[(*it).l.name];
					//cout<<tmploc.name<<" found"<<endl;


					NNC_Polyhedron invar;
					invar.add_space_dimensions_and_embed(a_lst.aut_arr.begin()->cntr_var_lst.cntr_var_arr.size());
					//invar.add_constraints(tmploc.invariants);
					invar=invar^tmploc.invariants;
					//add_trivial_constraints_to_poly(invar);
					//cout<<"Invariant:"<<invar<<endl;


					//add_trivial_constraints_to_poly((*it).poly);


					//if(invar.contains((*it).poly))
					//{
						//cout<<"Before:"<<(*it).poly<<endl;

						tmp_poly=(*it).poly;
						tmp_poly.intersection_assign(invar);
						add_trivial_constraints_to_poly(tmp_poly);
						//cout<<"After:"<<tmp_poly<<endl;


						//take time elapse by negative rate
						NNC_Polyhedron rate_poly;
						rate_poly.add_space_dimensions_and_embed(a_lst.aut_arr.begin()->cntr_var_lst.cntr_var_arr.size());


						//rate_poly.add_constraints(tmploc.rate);
						rate_poly=rate_poly^tmploc.rate;
						//cout<<"Rate poly:"<<rate_poly<<endl;




						//cout<<"tmp_poly:"<<(*it).poly<<endl;
						//cout<<"Rate poly:"<<rate_poly<<endl;
						tmp_poly.time_elapse_assign(rate_poly);
						cout<<"After 0st time elapse:"<<tmp_poly<<endl;
						//cout<<"After first location time elapse:"<<tmp_poly<<endl;

						add_trivial_constraints_to_poly(tmp_poly);

						cout<<"After pre location time elapse:"<<tmp_poly<<endl;





						//take anding of this with invariant of this location
						tmp_poly.intersection_assign(invar);
						add_trivial_constraints_to_poly(tmp_poly);
						cout<<"After intersecting with invariants of pre location:"<<tmp_poly<<endl;

						//replace updation vector of the edge in the representation of polyhedron
						/*for(Constraint_System_const_iterator csit=(*ittt).updates.begin();csit!=(*ittt).updates.end();csit++)
						{
							tmp_poly.add_constraint(*csit);
						}*/

						//cout<<"Updates of transition:"<<(*ittt).updates<<endl;


						if(tmp_poly.is_empty())
						{
								cout<<"Got empty polytope after updates are performed:"<<endl;
								//action has to be taken

						}










						/*tmp_poly.add_constraints((*ittt).updates);
						add_trivial_constraints_to_poly(tmp_poly);*/
						//cout<<"After adding updates:"<<tmp_poly<<endl;






						//take anding of this with the guards of selected edge


						//cout<<"Guards:"<<(*ittt).guards<<endl;
						//tmp_poly.add_constraints((*ittt).guards);
						tmp_poly=tmp_poly^(*ittt).guards;

						add_trivial_constraints_to_poly(tmp_poly);
						cout<<"After applying guards:"<<tmp_poly<<endl;

						//int idd;
						//scanf("%d",&idd);


						//transform tmp_poly's constraint_system with updates i.e. replace for every occurence of left with right

						tmp_poly=apply_Updates(tmp_poly,(*ittt).updates);

						//tmp_poly.add_constraints((*ittt).updates);
						tmp_poly=tmp_poly^(*ittt).updates;

						add_trivial_constraints_to_poly(tmp_poly);
						cout<<"After applying updates:"<<tmp_poly<<endl;
						//cout<<"Updates:"<<(*ittt).updates<<endl;


						//time elapse with rate of pre location take anding of this with the invariant of the pre location

						map<string,Location>::iterator itk=(*itt).loc_to_Location.find((*ittt).post);
						if(itk!=(*itt).loc_to_Location.end())
						{

							Location *locit;
							locit=&(*itk).second;
							/*for(Constraint_System_const_iterator cssit=(*locit).invariants.begin();cssit!=(*locit).invariants.end();cssit++)
							{
								tmp_poly.add_constraint(*cssit);
							}*/
							//tmp_poly.add_constraints((*locit).invariants);
							tmp_poly=tmp_poly^(*locit).invariants;
							add_trivial_constraints_to_poly(tmp_poly);
							cout<<"After checking invariants of the post location:"<<tmp_poly<<endl;

							//evolve with the time elapse relation of pre

							NNC_Polyhedron rate_poly1;
							rate_poly1.add_space_dimensions_and_embed(a_lst.aut_arr.begin()->cntr_var_lst.cntr_var_arr.size());
							//cout<<"Rate:"<<tmploc.rate<<endl;
							//rate_poly1.add_constraints((*locit).rate);
							rate_poly1=rate_poly1^(*locit).rate;

							//cout<<"Rate poly:"<<rate_poly<<endl;
							tmp_poly.time_elapse_assign(rate_poly1);
							add_trivial_constraints_to_poly(tmp_poly);

							cout<<"After post time elapse:"<<tmp_poly<<endl;



							//again take anding with invariants
							//tmp_poly.add_constraints((*locit).invariants);
							tmp_poly=tmp_poly^(*locit).invariants;
							add_trivial_constraints_to_poly(tmp_poly);

							cout<<"After checking invariants of post location:"<<tmp_poly<<endl;

							tmpstate.l=(*locit);


						}

						//push back this state to the returning state vector
						tmpstate.poly=tmp_poly;
						add_trivial_constraints_to_poly(tmpstate.poly);
						//cout<<"Output:"<<tmp_poly<<endl;
						if(!tmp_poly.is_empty())
						{
							//cout<<"Here:"<<tmp_poly<<endl;
							ret.push_back(tmpstate);
						}
					//}
					//else
					//{
					//	cout<<"Invariant doesn't carry poly:"<<endl;
					//}
				}

			}

		}
		rt.push_back(ret);
	}
	return rt;

}




bool is_Reachable_by_backward_fixpoint_computation(vector<vector<State> > R_f,vector<vector<State> > R_i,int max_iterations,Automaton_List &a_lst)
{
	vector<vector<State> > R_old,R_cur,R;
	R_cur=R_f;
	int it=0;
	//cout<<"In isreachable:"<<endl;
	//cout<<"Is inter phi:"<<is_intersection_phi(R_cur,R_i)<<endl;
	//cout<<"Is subset of:"<<is_subset_of(R_cur,R_old)<<endl;
	while(is_intersection_phi(R_cur,R_i)==true && is_subset_of(R_cur,R_old)!=true && it<max_iterations)
	{
		R=pre(R_cur,a_lst);

		printR(R,it+1);
		//cout<<"Pre calculated:"<<endl;
		//R_old=take_union(R_old,R_cur);
		R_old=R_old+R_cur;
		R_cur=R;
		it++;
		//cout<<"Size:"<<R_old.size()<<endl;
	}
	cout<<"It:"<<it<<endl;
	if(it==max_iterations)
		cout<<"Max limit reached:"<<endl;
	//printR(R_cur,0);
	//printR(R_old,0);
	cout<<is_subset_of(R_cur,R_old)<<endl;

	return !(is_intersection_phi(R_cur,R_i));
}


bool is_Reachable_by_forward_fixpoint_computation(vector<vector<State> > R_f,vector<vector<State> > R_i,int max_iterations,Automaton_List &a_lst)
{
	vector<vector<State> > R_old,R_cur,R;
	R_cur=R_i;
	int it=0;
	//cout<<"In isreachable:"<<endl;
	//cout<<"Is inter phi:"<<is_intersection_phi(R_cur,R_i)<<endl;
	//cout<<"Is subset of:"<<is_subset_of(R_cur,R_old)<<endl;
	while(is_intersection_phi(R_cur,R_f)==true && is_subset_of(R_cur,R_old)!=true && it<max_iterations)
	{
		R=post(R_cur,a_lst);

		printR(R,it+1);

		//R_old=take_union(R_old,R_cur);
		R_old=R_old+R_cur;
		R_cur=R;
		it++;
		//cout<<"Size:"<<R_old.size()<<endl;
	}
	cout<<"It:"<<it<<endl;
	if(it==max_iterations)
		cout<<"Max limit reached:"<<endl;
	return !(is_intersection_phi(R_cur,R_f));
}

