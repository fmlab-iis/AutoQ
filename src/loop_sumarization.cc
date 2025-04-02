#include "autoq/loop_sumarization.hh"
#include "autoq/aut_description.hh"
#include "autoq/util/string.hh"
#include <queue>

template<typename Symbol>
void execute_loop(std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, ParameterMap& params, 
                const AUTOQ::regexes& regexes, const std::sregex_iterator& END, std::smatch match_pieces){
    if(params["loop"] == "manual"){
        int start = std::stoi(match_pieces[2].str());
        int end = std::stoi(match_pieces[3].str());
        for(int i = start; i <= end; i++){
            for(const std::string& line : loop_body){
                aut.single_gate_execute(line, regexes, END);
            }
        }
        return;
    }
    if(params["loop"] == "symbolic"){
        aut = symbolic_loop<Symbol>(loop_body, aut, regexes);
    }
}

template<typename Symbol>
AUTOQ::Automata<AUTOQ::Symbol::Symbolic> initial_abstraction(AUTOQ::Automata<Symbol>& aut, AbstractionMap<Symbol>& alpha){
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T;
    T.name = aut.name + "_loopsum";
    T.finalStates = aut.finalStates;
    T.stateNum = aut.stateNum;
    T.qubitNum = aut.qubitNum;
    T.vars = aut.vars; // ?
    T.constraints = aut.constraints; // ?
    T.hasLoop = aut.hasLoop;
    T.isTopdownDeterministic = aut.isTopdownDeterministic;
    T.transitions = {};
    int i = 0;
    for(auto& transition : aut.transitions){
        if(transition.first.is_internal()){
            AUTOQ::Symbol::Symbolic symbol = transition.first.symbol().qubit();
            AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({symbol, transition.first.tag()});
            T.transitions[tag] = transition.second;
        }
        if(transition.first.is_leaf()){
            for(const auto& out : transition.second){
                auto q = out.first;
                auto res = alpha.find(q);
                if(res == alpha.end()){
                    // create new symbolic state
                    AUTOQ::Complex::SymbolicComplex c = AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor("symbolic_" + std::to_string(i++));
                    AUTOQ::Symbol::Symbolic symbol = AUTOQ::Symbol::Symbolic(c);
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({symbol, transition.first.tag()});
                    T.transitions[tag][out.first] = out.second;
                    alpha[q] = symbol;
                } else {
                    // use existing symbolic variable
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({res->second, transition.first.tag()});
                    T.transitions[tag][out.first] = out.second;
                }
            }
        }
    }
    return T;
}










AUTOQ::Symbol::Symbolic eval_mapping(const AUTOQ::Symbol::Symbolic& symbol, SymbolicMap& sigma, SymbolicMap& tau){
    AUTOQ::Symbol::Symbolic result = symbol;
    (void)tau;
    (void)sigma;
    return result;
}

AUTOQ::Automata<AUTOQ::Symbol::Symbolic> refinement(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& T, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& Tref, SymbolicMap& sigma, SymbolicMap& tau){
    // create automata product synchronized by colors
    // a transition is created if Colors1 & Colors2 != 0 (meaning the intersection of colors is not empty)
    // for leaf transitions, eval_mapping() is used to evaluate the symbolic variable in SymbolTag

    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> product;
    product.qubitNum = T.qubitNum;
    product.vars = T.vars;
    product.constraints = T.constraints;
    product.hasLoop = T.hasLoop;
    product.isTopdownDeterministic = T.isTopdownDeterministic;
    product.transitions = {};
    
    using StateMap = std::map<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State>;

    std::cout << "---------------------------------------------------------" << std::endl;
    std::cout << "TREF AUTOMATON" << std::endl;
    Tref.print_aut();
    std::cout << "---------------------------------------------------------" << std::endl;
    std::cout << "T AUTOMATON" << std::endl;
    T.print_aut();
    std::cout << "---------------------------------------------------------" << std::endl;

    using TagMap = std::map<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State, std::set<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::StateVector>>;
    using ColorTransitions = std::map<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::Tag, TagMap>;
    using LeafTransitions = std::map<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag, TagMap>;
    using LevelTransitions = std::map<long int, ColorTransitions>;
    LevelTransitions lhs, rhs;
    LeafTransitions lhs_leaf, rhs_leaf;
    for(auto& t1 : T.transitions){
        if(t1.first.is_leaf()){
            auto& color_set = t1.first.tag();
            auto& symbol = t1.first.symbol();
            for(auto& out : t1.second){
                lhs_leaf[{symbol, color_set}][out.first] = out.second;
            }
        }
        else{
            long int qubit = static_cast<long int>(t1.first.symbol().qubit());
            auto color_set = t1.first.tag();
            int index = 1;
            while(color_set > 0){
                if(color_set & 1){
                    for(auto& out : t1.second){
                        lhs[qubit][index][out.first] = out.second;
                    }
                }
                color_set >>= 1;
                index++;
            }
        }
    }
    for(auto& t2 : Tref.transitions){
        if(t2.first.is_leaf()){
            auto& color_set = t2.first.tag();
            auto& symbol = t2.first.symbol();
            for(auto& out : t2.second){
                rhs_leaf[{symbol, color_set}][out.first] = out.second;
            }
        }
        else{
            long int qubit = static_cast<long int>(t2.first.symbol().qubit());
            auto color_set = t2.first.tag();
            int index = 1;
            while(color_set > 0){
                if(color_set & 1){
                    for(auto& out : t2.second){
                        rhs[qubit][index][out.first] = out.second;
                    }
                }
                color_set >>= 1;
                index++;
            }
        }
    }
    StateMap lhs_to_prod;
    StateMap rhs_to_prod;
    StateMap prod_to_lhs;
    StateMap prod_to_rhs;
    
    // add all initial states to corresponding maps
    int64_t state_counter = 1;
    for(auto& roots_lhs : T.finalStates){
        for(auto& root_rhs : Tref.finalStates){
            lhs_to_prod[roots_lhs] = state_counter;
            rhs_to_prod[root_rhs] = state_counter;
            prod_to_lhs[state_counter] = roots_lhs;
            prod_to_rhs[state_counter] = root_rhs;
            product.finalStates.emplace_back(state_counter);
            state_counter++;
        }
    }

    // NOW lhs and rhs are divided by levels and each respective color (not a bitset anymore)
    // the product goes by each level, creates a product synchronized by colors
    // because the colors are not sets anymore, we dont have to check for empty intersection
    // this does not yet process leaf transitions

    for(int level = 0; level <= T.qubitNum; level++){
        for(auto it1 = lhs[level].begin(), it2 = rhs[level].begin(); it1 != lhs[level].end() && it2 != rhs[level].end(); ++it1, ++it2){
            //now map<state, set<state_vector>>
            auto& lhs_transitions = it1->second;
            auto& rhs_transitions = it2->second;
            auto color = it1->first;

            // the parents should always be already in the maps
            // so that leaves creating new child states
            for(const auto& [lhs_state, lhs_set] : lhs_transitions){
                auto lhs_in_prod = lhs_to_prod[lhs_state];
                auto rhs_in_prod = rhs_transitions.find(prod_to_rhs[lhs_in_prod]);
                auto& rhs_set = rhs_in_prod->second;
                // iterate over the sets and over the StateVectors
                for(const auto& lhs_state_vector : lhs_set){
                    for(const auto& rhs_state_vector : rhs_set){
                        AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::StateVector prod_state_vector;
                        for(auto state_it1 = lhs_state_vector.begin(), state_it2 = rhs_state_vector.begin(); state_it1 != lhs_state_vector.end() && state_it2 != rhs_state_vector.end(); ++state_it1, ++state_it2){
                            auto in1 = lhs_to_prod.find(*state_it1);
                            auto in2 = rhs_to_prod.find(*state_it2);
                            if(in1 == lhs_to_prod.end() || in2 == rhs_to_prod.end()){
                                // create new state
                                auto new_state = state_counter++;
                                lhs_to_prod[*state_it1] = new_state;
                                rhs_to_prod[*state_it2] = new_state;
                                prod_to_lhs[new_state] = *state_it1;
                                prod_to_rhs[new_state] = *state_it2;
                                if(std::find(prod_state_vector.begin(), prod_state_vector.end(), new_state) == prod_state_vector.end()){
                                    prod_state_vector.emplace_back(new_state);
                                }
                            } else {
                                // add to existing state
                                auto new_state = in1->second;
                                if(std::find(prod_state_vector.begin(), prod_state_vector.end(), new_state) == prod_state_vector.end()){
                                    prod_state_vector.emplace_back(new_state);
                                }
                            }
                        }
                        if(prod_state_vector.size() == 1){
                            prod_state_vector.emplace_back(prod_state_vector[0]);
                        }

                        product.transitions[{level, color}][lhs_in_prod].insert(prod_state_vector);
                    }
                }
            }
            
        }
    }

    std::cout << "LHS_LEAF TRANSITIONS:" << std::endl;
    for (const auto& [key, value] : lhs_leaf) {
        std::cout << "Symbol: " << key.first << ", Color Set: " << key.second << std::endl;
        for (const auto& [state, state_vectors] : value) {
            std::cout << "  State: " << state << std::endl;
        }
    }

    std::cout << "RHS_LEAF TRANSITIONS:" << std::endl;
    for (const auto& [key, value] : rhs_leaf) {
        std::cout << "Symbol: " << key.first << ", Color Set: " << key.second << std::endl;
        for (const auto& [state, state_vectors] : value) {
            std::cout << "  State: " << state << std::endl;
        }
    }

    // processing leaf transitions
    // needs colors, parent nodes 
    // the symbol variable is to be evaluated


    product.print_aut();
    return product;
}










template<typename Symbol>
AUTOQ::Automata<Symbol> post_process_sumarization(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& Tref, SymbolicMap& sigma, SymbolicMap& tau){
    AUTOQ::Automata<Symbol> result;
    (void)Tref;
    (void)sigma;
    (void)tau;
    // todo apply mapping back to values we had before


    return result;
}


template<typename Symbol>
AUTOQ::Automata<Symbol> symbolic_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, const AUTOQ::regexes& regexes){
    AbstractionMap<Symbol> alpha;
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T = initial_abstraction(aut, alpha);
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> Tref = T;
    SymbolicMap sigma{};
    SymbolicMap tau{};
    
    // start of main summarization loop
    do {

        T.print_aut();
        T = Tref;
        //execute gates
        for(const std::string& line : loop_body){
            T.single_gate_execute(line, regexes, std::sregex_iterator());
        }
        sigma.clear();
        tau.clear();

        // refinement after executing loop body
        Tref = refinement(T, Tref, sigma, tau);
        exit(0); // REMOVE AFTER REMOVE AFTER REMOVE AFTER REMOVE AFTER REMOVE AFTER REMOVE AFTER REMOVE AFTER REMOVE AFTER REMOVE AFTER REMOVE AFTER 
    } while(Tref != T); // found fix-point?
    // end of main summarization loop


    // post process the summarization result
    AUTOQ::Automata<Symbol> result = post_process_sumarization<Symbol>(Tref, sigma, tau);
    return result;
}



template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template void execute_loop<AUTOQ::Symbol::Concrete>(std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, ParameterMap&, const AUTOQ::regexes&, const std::sregex_iterator&, std::smatch match_pieces);
template void execute_loop<AUTOQ::Symbol::Symbolic>(std::vector<std::string>&,AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, ParameterMap&, const AUTOQ::regexes&, const std::sregex_iterator&, std::smatch match_pieces);
template AUTOQ::Automata<AUTOQ::Symbol::Concrete> symbolic_loop<AUTOQ::Symbol::Concrete>(const std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, const AUTOQ::regexes&);
template AUTOQ::Automata<AUTOQ::Symbol::Symbolic> symbolic_loop<AUTOQ::Symbol::Symbolic>(const std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, const AUTOQ::regexes&);
template AUTOQ::Automata<AUTOQ::Symbol::Concrete> post_process_sumarization<AUTOQ::Symbol::Concrete>(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, SymbolicMap&, SymbolicMap&);
template AUTOQ::Automata<AUTOQ::Symbol::Symbolic> post_process_sumarization<AUTOQ::Symbol::Symbolic>(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, SymbolicMap&, SymbolicMap&);
