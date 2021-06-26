

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <queue>
#include "semant.h"
#include "utilities.h"


using std::queue;
using std::set;
extern int semant_debug;
extern char *curr_filename;

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}



ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {
    object_environment.enterscope();
    /* Fill this in */
    // copy the input classes
    this->user_defined_classes = classes;
    // append pre-defined classes
    install_basic_classes();
}

ClassTable::~ClassTable() {
    object_environment.exitscope();
}

void ClassTable::construct_graph() {
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        class__class* cls = dynamic_cast<class__class*>(classes->nth(i));
        graph[cls->get_parent()].emplace_back(cls->get_name());
        if (cls->get_parent() != No_class) {
            degree[cls->get_name()]++;
        }
        parent[cls->get_name()] = cls->get_parent();
    }
}

void ClassTable::check_inheritance() {
    // gather all classes symbols
    // for inheritance checking
    check_class_redefinition();
    if (errors()) return;
    // check whether class main exists
    check_main_class();
    if (errors()) return;

    // merge two lists
    for (int i = user_defined_classes->first(); user_defined_classes->more(i); i = user_defined_classes->next(i)) {
        classes = list_node<Class_>::append(classes,single_Classes(user_defined_classes->nth(i)));
    }

    for (int i = basic_classes->first(); basic_classes->more(i); i = basic_classes->next(i)) {
        classes = list_node<Class_>::append(classes,single_Classes(basic_classes->nth(i)));
    }

    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        auto cls = dynamic_cast<class__class*>(classes->nth(i));
        symbol_to_class[cls->get_name()] = cls;
    }
    // construct inheritance dependency graph
    construct_graph();
    // first check all classes' parent is well-defined
    check_all_parent_defined();
    if (errors()) return;
    // next check that the graph is acyclic
    check_graph_acyclic();
    if (errors()) return;
}

void ClassTable::check_main_class() {
    if (!user_defined_classes_set.count(Main)) {
        auto& stream = semant_error();
        stream << "class Main is not defined." << endl;
    }
}

void ClassTable::check_all_parent_defined() {
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        class__class* cls = dynamic_cast<class__class*>(classes->nth(i));
        if (cls->get_parent() != No_class && !basic_classes_set.count(cls->get_parent()) && !user_defined_classes_set.count(cls->get_parent())) {
            // parent class is not defined
            // report error
            auto& stream = semant_error(cls);
            stream << "class " << cls->get_name() << " inherits from an undefined parent class" << cls->get_parent() << endl;
        } else if (cls->get_parent() == cls->get_name()) {
            auto& stream = semant_error(cls);
            stream << "Class " << cls->get_name() << " cannot inherit class " << cls->get_name() << "." << endl;
        } else if (cls->get_parent() == Int) {
            auto& stream = semant_error(cls);
            stream << "Class " << cls->get_name() << " cannot inherit class " << Int << "." << endl;
        } else if (cls->get_parent() == Str) {
            auto& stream = semant_error(cls);
            stream << "Class " << cls->get_name() << " cannot inherit class " << Str << "." << endl;
        } else if (cls->get_parent() == Bool) {
            auto& stream = semant_error(cls);
            stream << "Class " << cls->get_name() << " cannot inherit class " << Bool << "." << endl;
        } else if (cls->get_parent() == SELF_TYPE) {
            auto& stream = semant_error(cls);
            stream << "Class " << cls->get_name() << " cannot inherit class " << SELF_TYPE << "." << endl;
        }
    }
}

void ClassTable::check_graph_acyclic() {
    // if topological sorting succeeds
    // then the graph is acyclic
    queue<Symbol> q;
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        class__class* cls = dynamic_cast<class__class*> (classes->nth(i));
        if (degree[cls->get_name()] == 0) {
            q.push(cls->get_name());
        }
    }
    int count = 0;
    while (q.size()) {
        auto cls = q.front();
        q.pop();
        count++;
        for (const auto& child:graph[cls]) {
            degree[child]--;
            if (degree[child] == 0) {
                q.push(child);
            }
        }
    }
    if (count != classes->len()) {
        // topological sort failed
        // report error
        auto& err_stream = semant_error();
        err_stream << "class inheritance dependency graph is cyclic" << endl;
    }
}

void ClassTable::check_class_redefinition() {
    for (int i = user_defined_classes->first(); user_defined_classes->more(i); i = user_defined_classes->next(i)) {
        class__class* cls = dynamic_cast<class__class*>(user_defined_classes->nth(i));
        if (basic_classes_set.count(cls->get_name())) {
            auto& err_stream = semant_error(cls);
            err_stream << "Redefinition of basic class "<<cls->get_name() << "." << endl;
            continue;
        } else if (user_defined_classes_set.count(cls->get_name())) {
            auto& err_stream = semant_error(cls);
            err_stream << "Redefinition of class "<<cls->get_name() << "." << endl;
            continue;
        }
        user_defined_classes_set.insert(cls->get_name());
    }
}

void ClassTable::add_method_declarations(Symbol node,Symbol parent) {
    if (parent != No_class) {
        function_environment[node] = function_environment[parent];
    }
    auto cls = symbol_to_class[node];
    current_class = cls;
    cls->add_method_declarations(this);
    for (auto& child:graph[node]) {
        add_method_declarations(child,node);
    }
}

void ClassTable::add_attr_declarations(Symbol node) {
    vector<class__class*> involved_classes;
    while (node != No_class) {
        involved_classes.push_back(symbol_to_class[node]);
        node = parent[node];
    }
    reverse(involved_classes.begin(),involved_classes.end());
    for (auto cls:involved_classes) {
        cls->add_attr_declarations(this);
    }
}

void ClassTable::type_checking_and_annotation() {
    // traversal the inheritance graph
    // gather all method declarations
    add_method_declarations(Object,No_class);
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {

        class__class* cls = dynamic_cast<class__class*>(classes->nth(i));
        current_class = cls;
        object_environment.enterscope();
        add_attr_declarations(cls->get_name());
        object_environment.addid(self,SELF_TYPE);
        cls->semant(this);
        object_environment.exitscope();
    }
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        class__class* cls = dynamic_cast<class__class*>(classes->nth(i));
        current_class = cls;
        function_environment[cls->get_name()].exitscope();
    }
}

bool ClassTable::inheritance_leq(Symbol a,Symbol b) {
    if (a == SELF_TYPE) a = get_current_class_name();
    if (b == SELF_TYPE) b = get_current_class_name();
    if (a == b) return true;
    for (auto& child:graph[b]) {
        if (inheritance_leq(a,child)) return true;
    }
    return false;
}

Symbol ClassTable::least_common_ancestor(Symbol a,Symbol b) {
    if (a == SELF_TYPE) a = get_current_class_name();
    if (b == SELF_TYPE) b = get_current_class_name();
    set<Symbol> visit;
    while (a != No_class) {
        visit.insert(a);
        a = parent[a];
    }
    while (b != No_class) {
        if (visit.count(b)) return b;
        b = parent[b];
    }
    cerr << "LCA for " << a << " " << b << " failed" << endl;
    return Object;
}

void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);
    basic_classes = list_node<Class_>::append(basic_classes,single_Classes(Object_class));
    basic_classes = list_node<Class_>::append(basic_classes,single_Classes(IO_class));
    basic_classes = list_node<Class_>::append(basic_classes,single_Classes(Int_class));
    basic_classes = list_node<Class_>::append(basic_classes,single_Classes(Bool_class));
    basic_classes = list_node<Class_>::append(basic_classes,single_Classes(Str_class));
    basic_classes_set.insert(Object);
    basic_classes_set.insert(IO);
    basic_classes_set.insert(Int);
    basic_classes_set.insert(Bool);
    basic_classes_set.insert(Str);
    basic_classes_set.insert(SELF_TYPE);
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 

bool ClassTable::has_type(Symbol type) {
    return user_defined_classes_set.count(type) || basic_classes_set.count(type) || type == SELF_TYPE;
}

/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    ClassTable classtable(classes);

    /* some semantic analysis code may go here */
    classtable.check_inheritance();
    if (classtable.errors()) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
    // type checking & gathering
    classtable.type_checking_and_annotation();
    if (classtable.errors()) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}

void class__class::add_method_declarations(ClassTable *class_table) {
    class_table->function_environment[class_table->get_current_class_name()].enterscope();
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        features->nth(i)->add_method_declarations(class_table);
    }
}

void class__class::add_attr_declarations(ClassTable *class_table) {
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        features->nth(i)->add_attr_declarations(class_table);
    }
}

Symbol branch_class::semant(ClassTable *class_table) {
    class_table->object_environment.enterscope();
    class_table->object_environment.addid(name,type_decl);
    auto T = expr->semant(class_table);
    class_table->object_environment.exitscope();
    return T;
}

void method_class::semant(ClassTable *class_table) {
    class_table->object_environment.enterscope();
    const auto& res = class_table->function_environment[class_table->get_current_class_name()].lookup(name);
    if (!res.ok) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "method " << name << " type error" << endl;
        return;
    }
    const auto& Ts = res.dat;
    auto T0 = Ts.back();

    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        int index = i - formals->first();
        auto formal = dynamic_cast<formal_class*> (formals->nth(i));
        if (formal->get_name() == self) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "'self' cannot be the name of a formal parameter" << endl;
            continue;
        }
        if (class_table->object_environment.probe(formal->get_name()).ok) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "Formal parameter" << formal->get_name() << " is multiply defined." << endl;
            continue;
        }
        class_table->object_environment.addid(formal->get_name(),Ts[index]);
    }

    auto T0_prime = expr->semant(class_table);
    if ((T0 == SELF_TYPE && T0_prime != SELF_TYPE && T0_prime != No_type)
        || (T0 != SELF_TYPE && T0_prime != No_type && !class_table->inheritance_leq(T0_prime,T0))) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "Inferred return type " << T0_prime << " of method " << name << " does not conform to declared return type " << T0 << "." << endl;
    }

    class_table->object_environment.exitscope();
}

void method_class::add_method_declarations(ClassTable *class_table) {
    auto& table = class_table->function_environment[class_table->get_current_class_name()];
    vector<Symbol> symbols;
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        auto T = formals->nth(i)->get_type_decl();
        if (!class_table->has_type(T)) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "Formal parameter " << formals->nth(i)->get_name() << " has undefined type " << T << "." << endl;
            return;
        } else if (T == SELF_TYPE) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "Formal parameter " << formals->nth(i)->get_name() << " cannot have type SELF_TYPE." << endl;
            return;
        }
        symbols.push_back(T);
    }
    if (!class_table->has_type(return_type)) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "Undefined return type " << return_type << " in method " << name << "." << endl;
        return;
    }
    symbols.push_back(return_type);
    const auto& res = table.lookup(name);
    if (res.ok) {
        if (res.dat.size() != symbols.size()) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "Incompatible number of formal parameters in redefined method " << name << "." << endl;
            return;
        } else if (res.dat != symbols) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "Incompatible type of formal parameters in redefined method " << name << "." << endl;
            return;
        }
    }
    table.addid(name,symbols);
}

void attr_class::add_attr_declarations(ClassTable *class_table) {
    const auto& res = class_table->object_environment.lookup(name);
    if (res.ok) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "Attribute moo is an attribute of an inherited class." << endl;
    } else if (name == self) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "'self' cannot be the name of an attribute." << endl;
    } else {
        class_table->object_environment.addid(name, type_decl);
    }
}

void attr_class::semant(ClassTable *class_table) {
    auto T1 = init->semant(class_table);
    auto T0 = type_decl;
    if (T1 != No_type && !class_table->inheritance_leq(T1,T0)) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "attr init type error" << endl;
        // type it as an object
    }
}

Symbol assign_class::semant(ClassTable *class_table) {
    const auto& res = class_table->object_environment.lookup(name);
    if (!res.ok) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "object " << name << " is undefined !" << endl;
        // type it as an object
        this->type = Object;
        return Object;
    }
    if (name == self) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "Cannot assign to 'self'." << endl;
        // type it as an object
        this->type = Object;
        return Object;
    }
    auto T = res.dat;
    auto T_prime = expr->semant(class_table);
    if (class_table->inheritance_leq(T_prime,T)) {
        this->type = T_prime;
        return T_prime;
    } else {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "assign type error" << endl;
        this->type = Object;
        return Object;
    }
}

Symbol static_dispatch_class::semant(ClassTable *class_table) {
    auto T0 = expr->semant(class_table);
    auto T = type_name;
    if (!class_table->inheritance_leq(T0,T)) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "static dispatch type error" << endl;
        this->type = Object;
        return Object;
    }
    vector<Symbol> Ts;
    for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
        Ts.push_back(actual->nth(i)->semant(class_table));
    }
    const auto& res = class_table->function_environment[T].lookup(name);
    const auto& T_primes = res.dat;
    if (!res.ok || Ts.size() != T_primes.size() - 1) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "static dispatch wrong arguments number" << endl;
        this->type = Object;
        return Object;
    }
    for (int i = 0; i < Ts.size(); i++) {
        if (!class_table->inheritance_leq(Ts[i],T_primes[i])) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "static dispatch type error" << endl;
            this->type = Object;
            return Object;
        }
    }
    auto T_n_plus_1_prime = T_primes.back();
    Symbol T_n_plus_1;
    if (T_n_plus_1_prime == SELF_TYPE) {
        T_n_plus_1 = T0;
    } else {
        T_n_plus_1 = T_n_plus_1_prime;
    }
    this->type = T_n_plus_1;
    return T_n_plus_1;
}

Symbol dispatch_class::semant(ClassTable *class_table) {
    auto T0 = expr->semant(class_table);
    vector<Symbol> Ts;
    for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
        Ts.push_back(actual->nth(i)->semant(class_table));
    }
    Symbol T0_prime;
    if (T0 == SELF_TYPE) {
        T0_prime = class_table->get_current_class_name();
    } else {
        T0_prime = T0;
    }
    const auto& res = class_table->function_environment[T0_prime].lookup(name);
    const auto& T_primes = res.dat;
    if (!res.ok || Ts.size() != T_primes.size() - 1) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "dispatch wrong arguments number" << endl;
        this->type = Object;
        return Object;
    }
    for (int i = 0; i < Ts.size(); i++) {
        if (!class_table->inheritance_leq(Ts[i],T_primes[i])) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "dispatch type error" << endl;
            this->type = Object;
            return Object;
        }
    }
    auto T_n_plus_1_prime = T_primes.back();
    Symbol T_n_plus_1;
    if (T_n_plus_1_prime == SELF_TYPE) {
        T_n_plus_1 = T0;
    } else {
        T_n_plus_1 = T_n_plus_1_prime;
    }
    this->type = T_n_plus_1;
    return T_n_plus_1;
}

Symbol cond_class::semant(ClassTable *class_table) {
    auto T1 = pred->semant(class_table);
    if (T1 != Bool) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "if stmt's pred type is not bool" << endl;
        this->type = Object;
        return Object;
    }
    auto T2 = then_exp->semant(class_table);
    auto T3 = else_exp->semant(class_table);
    this->type = class_table->least_common_ancestor(T2,T3);
    return this->type;
}

Symbol loop_class::semant(ClassTable *class_table) {
    auto T1 = pred->semant(class_table);
    body->semant(class_table);
    if (T1 != Bool) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "loop stmt's pred type is not bool" << endl;
        this->type = Object;
        return Object;
    }
    this->type = Object;
    return Object;
}

Symbol typcase_class::semant(ClassTable *class_table) {
    expr->semant(class_table);
    vector<Symbol> T_primes;
    std::set<Symbol> exist_types;
    for (int i = cases->first(); cases->more(i); i = cases->next(i)) {
        auto T = cases->nth(i)->get_type_decl();
        if (exist_types.count(T)) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "Duplicate branch "<< T <<" in case statement." << endl;
            this->type = Object;
            return Object;
        }
        exist_types.insert(T);
        T_primes.push_back(cases->nth(i)->semant(class_table));
    }
    if (T_primes.size() == 0) {
        this->type = Object;
        return Object;
    }
    auto Union_T = T_primes[0];
    for (int i = 1; i < T_primes.size(); i++) {
        Union_T = class_table->least_common_ancestor(Union_T,T_primes[i]);
    }
    this->type = Union_T;
    return Union_T;
}

Symbol block_class::semant(ClassTable *class_table) {
    class_table->object_environment.enterscope();
    vector<Symbol> Ts;
    for (int i = body->first(); body->more(i); i = body->next(i)) {
        Ts.push_back(body->nth(i)->semant(class_table));
    }
    this->type = Ts.back();
    class_table->object_environment.exitscope();
    return this->type;
}

Symbol let_class::semant(ClassTable *class_table) {
    auto init_type = init->semant(class_table);
    if (identifier == self) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "'self' cannot be bound in a 'let' expression." << endl;
        type = Object;
        return Object;
    }
    if (init_type == No_type) {
        // let no init
        auto T0 = type_decl;
        Symbol T0_prime;
        T0_prime = T0;
        class_table->object_environment.enterscope();
        class_table->object_environment.addid(identifier,T0_prime);
        auto T1 = body->semant(class_table);
        class_table->object_environment.exitscope();
        type = T1;
        return T1;
    } else {
        // let init
        auto T0 = type_decl;
        Symbol T0_prime;
        T0_prime = T0;
        auto T1 = init_type;
        if (!class_table->inheritance_leq(T1,T0_prime)) {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "let init type error" << endl;
            this->type = Object;
            return Object;
        }
        class_table->object_environment.enterscope();
        class_table->object_environment.addid(identifier,T0_prime);
        auto T2 = body->semant(class_table);
        class_table->object_environment.exitscope();
        type = T2;
        return T2;
    }
}

Symbol plus_class::semant(ClassTable *class_table) {
    auto T1 = e1->semant(class_table);
    auto T2 = e2->semant(class_table);
    if (T1 != Int || T2 != Int) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "plus type error" << endl;
        this->type = Object;
        return Object;
    } else {
        this->type = Int;
        return Int;
    }
}

Symbol sub_class::semant(ClassTable *class_table) {
    auto T1 = e1->semant(class_table);
    auto T2 = e2->semant(class_table);
    if (T1 != Int || T2 != Int) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "sub type error" << endl;
        this->type = Object;
        return Object;
    } else {
        this->type = Int;
        return Int;
    }
}

Symbol mul_class::semant(ClassTable *class_table) {
    auto T1 = e1->semant(class_table);
    auto T2 = e2->semant(class_table);
    if (T1 != Int || T2 != Int) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "mul type error" << endl;
        this->type = Object;
        return Object;
    } else {
        this->type = Int;
        return Int;
    }
}

Symbol divide_class::semant(ClassTable *class_table) {
    auto T1 = e1->semant(class_table);
    auto T2 = e2->semant(class_table);
    if (T1 != Int || T2 != Int) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "divide type error" << endl;
        this->type = Object;
        return Object;
    } else {
        this->type = Int;
        return Int;
    }
}

Symbol neg_class::semant(ClassTable *class_table) {
    auto T = e1->semant(class_table);
    if (T != Int) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "neg type error" << endl;
        this->type = Object;
        return Object;
    } else {
        this->type = Int;
        return Int;
    }
}

Symbol lt_class::semant(ClassTable *class_table) {
    auto T1 = e1->semant(class_table);
    auto T2 = e2->semant(class_table);
    if (T1 != Int || T2 != Int) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "lt type error" << endl;
        this->type = Object;
        return Object;
    } else {
        this->type = Bool;
        return Bool;
    }
}

Symbol eq_class::semant(ClassTable *class_table) {
    auto T1 = e1->semant(class_table);
    auto T2 = e2->semant(class_table);

    if ((T1 == Int || T1 == Bool || T1 == Str) && (T2 == Int || T2 == Bool || T2 == Str)) {
        if (T1 == T2) {
            this->type = Bool;
            return Bool;
        } else {
            auto& err_stream = class_table->semant_error(class_table->current_class);
            err_stream << "eq type error" << endl;
            this->type = Object;
            return Object;
        }
    } else {
        this->type = Bool;
        return Bool;
    }
}

Symbol leq_class::semant(ClassTable *class_table) {
    auto T1 = e1->semant(class_table);
    auto T2 = e2->semant(class_table);
    if (T1 != Int || T2 != Int) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "leq type error" << endl;
        this->type = Object;
        return Object;
    } else {
        this->type = Bool;
        return Bool;
    }
}

Symbol comp_class::semant(ClassTable *class_table) {
    auto T = e1->semant(class_table);
    if (T != Bool) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "NOT type error" << endl;
        this->type = Object;
        return Object;
    } else {
        this->type = Bool;
        return Bool;
    }
}

Symbol int_const_class::semant(ClassTable *class_table) {
    this->type = Int;
    return Int;
}

Symbol bool_const_class::semant(ClassTable *class_table) {
    this->type = Bool;
    return Bool;
}

Symbol string_const_class::semant(ClassTable *class_table) {
    this->type = Str;
    return Str;
}

Symbol new__class::semant(ClassTable *class_table) {
    auto T = type_name;
    if (!class_table->has_type(T)) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "'new' used with undefined class" << T << "." << endl;
        type = Object;
        return Object;
    }
    Symbol T_prime;
    T_prime = T;
    type = T_prime;
    return T_prime;
}

Symbol isvoid_class::semant(ClassTable *class_table) {
    e1->semant(class_table);
    type = Bool;
    return Bool;
}

Symbol no_expr_class::semant(ClassTable *class_table) {
    type = No_type;
    return No_type;
}

Symbol object_class::semant(ClassTable *class_table) {
    const auto& res = class_table->object_environment.lookup(name);
    auto T = res.dat;
    if (!res.ok) {
        auto& err_stream = class_table->semant_error(class_table->current_class);
        err_stream << "object " << name << " is undefined !" << endl;
        // type it as an object
        T = Object;
    }
    type = T;
    return T;
}

