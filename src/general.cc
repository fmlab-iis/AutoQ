#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include <numeric> // used in std::numeric_limits
#include <chrono> // used in remove_useless
#include <queue> // used in remove_useless

template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::operator*(Automata<Symbol> aut2) const {
    
    // Step 1. Modify the first-layer transitions of aut2 so that
    //         (1) there is only one root state, and
    //         (2) all colors in these transitions are disjoint.
    // But notice that we actually do not modify root states here
    // since these states will become the leaf states of aut1 eventually.
    // That is, we only modify the colors here.
    // One way is to simply recolor all these transitions such that
    // each color set uses only 1 bit.
    TopDownTransitions aut2_transitions_at_1st_layer;
    AUTOQ::Automata<Symbol>::Tag color = 1;
    int num_of_colors_used_in_aut2 = 0;
    for (auto it = aut2.transitions.cbegin(); it != aut2.transitions.cend() /* not hoisted */; /* no increment */) {
        if (it->first.is_internal() && it->first.symbol().qubit() == 1) {
            if (color == AUTOQ::Automata<Symbol>::Tag_MAX) {
                THROW_AUTOQ_ERROR("Colors are not enough!!!");
            }
            for (const auto &out_ins : it->second) {
                auto out = out_ins.first;
                for (const auto &in : out_ins.second) {
                    aut2_transitions_at_1st_layer[AUTOQ::Automata<Symbol>::SymbolTag(it->first.symbol(), AUTOQ::Automata<Symbol>::Tag(color))][out].insert(in);
                    num_of_colors_used_in_aut2++;
                    color <<= 1;
                }
            }
            aut2.transitions.erase(it++);    // or "it = aut2.transitions.erase(it)" since C++11
            // https://stackoverflow.com/a/8234813/11550178
        } else {
            ++it;
        }
    }
    for (const auto &t : aut2_transitions_at_1st_layer) {
        aut2.transitions[t.first] = t.second;
    }
    // Now "num_of_colors_used_in_aut2" denotes the number of bits for colors in aut2.

    // Step 2. For each leaf transition of aut1, we construct one "state-disjoint" copy of aut2,
    //         (1) whose root states are replaced with the top state of that leaf transition, and
    //         (2) whose colors of the first-layer transitions are prepended with the color of that leaf transition, and
    //         (3) whose leaf symbols are multiplied with the symbol of that leaf transition, and
    //         (4) finally we remove that leaf transition.
    auto aut = *this;
    TopDownTransitions transitions_to_be_appended;
    for (auto it = aut.transitions.cbegin(); it != aut.transitions.cend() /* not hoisted */; /* no increment */) {
        if (it->first.is_leaf()) {
            for (const auto &out_ins : it->second) {
                auto the_top_state_of_that_leaf_transition = out_ins.first; // (1)
                assert(out_ins.second == std::set<StateVector>({{}}));
                auto the_color_of_that_leaf_transition = it->first.tag(); // (2)
                int num_of_colors_used_in_that_leaf_transition = 0;
                auto tmp = the_color_of_that_leaf_transition;
                while (tmp > 0) {
                    num_of_colors_used_in_that_leaf_transition++;
                    tmp >>= 1;
                }
                if (num_of_colors_used_in_that_leaf_transition * num_of_colors_used_in_aut2 > std::numeric_limits<Tag>::digits) {
                    THROW_AUTOQ_ERROR("The shifted color is out of range!!!");
                }
                for (const auto &t : aut2.transitions) {
                    if (t.first.is_leaf()) { // (3)
                        auto &ref = transitions_to_be_appended[AUTOQ::Automata<Symbol>::SymbolTag(it->first.symbol() * t.first.symbol(), t.first.tag())];
                        for (const auto &out_ins : t.second) {
                            auto out = out_ins.first;
                            out += aut.stateNum;
                            auto &container = ref[out];
                            for (auto in : out_ins.second) {
                                for (unsigned i=0; i<in.size(); i++) {
                                    in[i] += aut.stateNum;
                                }
                                container.insert(in);
                            }
                        }
                    } else if (t.first.symbol().qubit() == 1) { // (1)(2)
                        int counter = 0;
                        Tag new_color_pair = 0;
                        auto tmpi = the_color_of_that_leaf_transition;
                        for (int i=0; i<num_of_colors_used_in_that_leaf_transition; i++) {
                            auto tmpj = t.first.tag();
                            for (int j=0; j<num_of_colors_used_in_aut2; j++) {
                                if (tmpi & tmpj & 1)
                                    new_color_pair |= static_cast<Tag>(1) << counter;
                                counter++;
                                tmpj >>= 1;
                            }
                            tmpi >>= 1;
                        }
                        auto &ref = transitions_to_be_appended[AUTOQ::Automata<Symbol>::SymbolTag(aut.qubitNum + t.first.symbol().qubit(), new_color_pair)];
                        for (const auto &out_ins : t.second) {
                            auto &container = ref[the_top_state_of_that_leaf_transition];
                            for (auto in : out_ins.second) {
                                for (unsigned i=0; i<in.size(); i++) {
                                    in[i] += aut.stateNum;
                                }
                                container.insert(in);
                            }
                        }
                    } else { // other transitions
                        auto &ref = transitions_to_be_appended[AUTOQ::Automata<Symbol>::SymbolTag(aut.qubitNum + t.first.symbol().qubit(), t.first.tag())];
                        for (const auto &out_ins : t.second) {
                            auto out = out_ins.first;
                            out += aut.stateNum;
                            auto &container = ref[out];
                            for (auto in : out_ins.second) {
                                for (unsigned i=0; i<in.size(); i++) {
                                    in[i] += aut.stateNum;
                                }
                                container.insert(in);
                            }
                        }
                    }
                }
            }
            aut.transitions.erase(it++); // (4)
            aut.stateNum += aut2.stateNum;
        } else {
            ++it;
        }
    }
    for (const auto &t : transitions_to_be_appended) {
        aut.transitions[t.first] = t.second;
    }
    aut.qubitNum += aut2.qubitNum;
    aut.reduce();
    for (const auto &var : aut2.vars)
        aut.vars.insert(var);
    return aut;
}

template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::operator||(const Automata<Symbol> &o) const {
    if (this->qubitNum == 0) return o;
    if (o.qubitNum == 0) return *this;

    Automata<Symbol> result;
    result = *this;
    result.name = "operator||";
    if (result.qubitNum != o.qubitNum) {
        THROW_AUTOQ_ERROR("Two automata of different numbers of qubits cannot be unioned together.");
    }
    result.stateNum += o.stateNum;
    // TODO: How to check if the two input automata have different k's?

    for (const auto &t : o.transitions) {
        auto &container = result.transitions[t.first];
        for (const auto &out_ins : t.second) {
            auto out = out_ins.first;
            out += this->stateNum;
            auto &sub_container = container[out];
            for (auto in : out_ins.second) {
                for (unsigned i=0; i<in.size(); i++) {
                    in[i] += this->stateNum;
                }
                sub_container.insert(in);
            }
        }
    }
    for (const auto &s : o.finalStates) {
        result.finalStates.push_back(s + this->stateNum);
    }
    result.reduce();
    for (const auto &var : o.vars)
        result.vars.insert(var);
    result.constraints += o.constraints;
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
    
    
    return result;
}

using namespace std;

std::map<int64_t,std::vector<std::pair<int64_t,std::set<std::vector<int64_t>>>>> next_transitions_hash;
int traverse(std::vector<int64_t> root_transition\
            , std::vector<std::list<int64_t>>& qubit_trans_hash\
            , std::map<int64_t,int>& valids\
            , int current_layer)
{
    if(root_transition.empty())
        return -1;
    if(current_layer == qubit_trans_hash.size()-1) //leaf layer
    {
        for(const auto& t : root_transition)
        {
            valids[t] = 1;
        }
        return 1;
    }

    cout<<"CURRENT_LAYER:"<<current_layer<<endl;
    cout<<"VALID:"<<endl;
    for(const auto& v : valids)
    {
        cout<<v.first<<":"<<v.second<<endl;
    }
    cout<<"ROOT_TRANSITION:"<<endl;
    for(const auto& r : root_transition)
    {
        cout<<r<<endl;
    }
    cout<<endl;

    
    for(const auto& t : root_transition)
    {
        if(valids[t] == -1)
            return -1;   //there's a path can reach the final state
    }


    //root_transition: list of transition idx under qubit [current_layer]
    //1 decompose into tags
    std::map<int64_t, std::list<int64_t>> tags;
    for(const auto& q : qubit_trans_hash[current_layer])   //q: state num
    {
        for(const auto& tags_child : next_transitions_hash[q])
        {
            int64_t cur_tag = tags_child.first;
            tags[cur_tag].push_back(q);
        }
    }

    for(auto& T:tags)
    {
        int64_t cur_tag = T.first;
        std::set<int64_t> set_of_next_transitions;
        for(const auto& q : T.second)
        {
            for(const auto& tags_child : next_transitions_hash[q])
            {
                if(tags_child.first == cur_tag)
                {
                    for(auto& childs : tags_child.second)
                    set_of_next_transitions.insert(childs.begin(),childs.end());
                }
            }
        }

        std::vector<int64_t> vec_next_transitions = {set_of_next_transitions.begin(),set_of_next_transitions.end()};
        int val = traverse(vec_next_transitions\
                    , qubit_trans_hash\
                    , valids
                    , current_layer+1);
        if(val == -1)
            return -1;
    }
    
    for(const auto& t : root_transition)
    {
        valids[t] = 1;
    }

    return 1; 
}


using AUTOQ::Util::Convert;

template <typename Symbol>
bool AUTOQ::Automata<Symbol>::operator!() const
{
    cout<<"operator!()"<<endl;
    vector<vector<pair<int,int>>> check_list; //qubit, node_idx, transition 
    
    //data needed: tag/qubit/child , node_idx is not needed


    

    std::map<int64_t,SymbolTag>   node_hash; //map[transition idx]
    next_transitions_hash.clear();
    std::map<int64_t,int> valids;
    std::vector<std::list<int64_t>> qubit_trans_hash; //vec[q-1] = {transitions with qubit index q}
    qubit_trans_hash.resize(this->qubitNum+2);  //0 for dummy list, qubitNum+1 for leaf transitions

    for(const auto &t : this->transitions)  
    {
        for(const auto &t2 : t.second)
        {
            
            node_hash[t2.first] = t.first;
            next_transitions_hash[t2.first] = std::vector<std::pair<int64_t,std::set<std::vector<int64_t>>>>{};
            valids[t2.first] = 0;

            int64_t cur_tag = t.first.tag();
            int64_t tag_bit = 1;
            while(cur_tag > 0)  //decompose the tag into bits
            {

                if(cur_tag & 1)
                {
                    next_transitions_hash[t2.first].push_back(make_pair(tag_bit, t2.second));
                }
                cur_tag >>= 1;
                tag_bit++;
            }

            if(t.first.is_leaf())
                qubit_trans_hash.back().push_back(t2.first);
            else
                qubit_trans_hash[static_cast<int>( t.first.symbol().qubit())].push_back(t2.first);
        } 
    }
    //list of transition -> map<tag, set<child>>

    std::vector<int64_t> root_transitions{};
    for(const auto& t : node_hash)
    {
        if(t.second.is_leaf())
            continue;
        if(t.second.symbol().qubit() == 1) 
        {
            root_transitions.push_back(t.first);
        }
    }



    return  traverse(root_transitions\
                    , qubit_trans_hash\
                    , valids\
                    , 1);
}



template <typename Symbol>
AUTOQ::Automata<Symbol> AUTOQ::Automata<Symbol>::operator&(const Automata<Symbol> &o) const {
    if (this->qubitNum == 0) return o; 
    if (o.qubitNum == 0) return *this;

    Automata<Symbol> result = *this;
    result.name = "operator&";
    if (result.qubitNum != o.qubitNum) {
        THROW_AUTOQ_ERROR("Two automata of different numbers of qubits cannot be unioned together.");
    }
    



    //Encode value  -> tag1*offset + tag2
    int color_offset = 0;
    for (const auto &t : this->transitions) {
        if(t.first.is_leaf())
            continue;
        if(t.first.tag() > color_offset)    
            color_offset = t.first.tag();  
    }
    color_offset = static_cast<int>(floor(log2(color_offset))+1);

    auto tag_encode = [&](const int64_t& a, const int64_t& b)->int64_t {
        return 1<<((b<<color_offset) + a);
    };
    auto state_encode = [&](const int64_t& a, const int64_t& b)->int64_t {
        return b*(1+this->stateNum) + a;
    };

    std::map<int64_t,set<StateVector>> valids;

    result.transitions.clear();
    for (const auto &t_other : o.transitions) {
        for(const auto &t_cur : this->transitions)
        {
            if(t_cur.first.symbol() != t_other.first.symbol())  
                continue;
            cout<<"SYMBOL:"<<endl;
            cout<<Convert::ToString(t_cur.first)<<endl;
            cout<<Convert::ToString(t_other.first)<<endl;
            int64_t new_tag = tag_encode(t_cur.first.tag(), t_other.first.tag());
            SymbolTag ST(t_cur.first.symbol(), new_tag);
            //traverse the node under this combination
            result.transitions.insert(pair<SymbolTag, map<State, set<StateVector>>>(ST, map<State, set<StateVector>>()));

            for(const auto &t2_cur : t_cur.second)
            {
                for(const auto &t2_other : t_other.second)
                {
                    cout<<"t2_cur:"<<t2_cur.first<<endl;
                    cout<<"t2_other:"<<t2_other.first<<endl;
                    int64_t new_state = state_encode(t2_cur.first, t2_other.first);

                    pair<State, std::set<StateVector>> to_insert = make_pair(new_state, std::set<StateVector>{});

                    StateVector child_cur = *t2_cur.second.begin();
                    StateVector child_other = *t2_other.second.begin();
                    StateVector child_new;
                    for(int i = 0 ; i < child_cur.size(); i++)
                    {
                        child_new.push_back(state_encode(child_cur[i], child_other[i]));
                    }
                    to_insert.second.insert(child_new);
                    result.transitions[t_cur.first].insert(to_insert);

                    if(t_cur.first.is_leaf())
                        result.finalStates.push_back(new_state);
                }
            }
            cout<<"NEW_TAG:"<<new_tag<<endl;
            result.stateNum++;
            
        }
    }
    cout<<"EXIT"<<endl;
    
    //result.reduce();
    //for (const auto &var : o.vars)
    //    result.vars.insert(var);
    //result.constraints += o.constraints;

    
    if (opLog) std::cout << __FUNCTION__ << "：" << stateNum << " states " << count_transitions() << " transitions\n";
    
    cout<<"END"<<endl;
    return result;
}


// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Predicate>;