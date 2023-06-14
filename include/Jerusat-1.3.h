// Macro guard
#ifndef JERUSAT1_3_SOLVER_CSE473_H
#define JERUSAT1_3_SOLVER_CSE473_H

// Files included
#include "SolverInterface.h"


/*============================================================================//
    Jerusat-1.3.h: header file - implementation of SolverInterface for
     Jerusat-1.3 program.

    Implementation: Shane J. Neph, June 2004, University of Washington
//============================================================================*/

struct Jerusat_1_3Solver : public SolverInterface {
    static std::string ExeName()
        { return("jerusat1.3"); }

    static std::string Name()
        { return("jerusat1.3"); }

    Jerusat_1_3Solver() : tmpFile_("jerusat1.3.stats"),
                          results_("jerusat1.3.results") { /* */ }

    virtual ~Jerusat_1_3Solver()
        { /* */ }

private:
    virtual std::vector<std::string> cleanFiles() const {
        std::vector<std::string> toRtn;
        toRtn.push_back(getTempFile());
        toRtn.push_back(getSolutionName());
        return(toRtn);
    }
    virtual bool evaluateReturn(int rtnVal);
    virtual std::string exe() const { return(ExeName() + " "); }
    virtual std::string getExeNameAndArgs(const std::string& dir,
                                          const std::string& wffFileName,
                                          long rand) {
        std::string toRtn = exe() + wffFileName;
        toRtn += std::string(" -seed ") + convert<std::string>(rand);
        toRtn += " >> " + getTempFile();
        return(dir + toRtn);
    }
    virtual std::string getExeNameAndArgs(const std::string& dir,
                                          const std::string& wffFileName,
                                          const std::string& options) {
        std::string toRtn = exe() + wffFileName;
        toRtn += (" ") + options;
        toRtn += " >> " + getTempFile();
        return(dir + toRtn);        
    }
    virtual std::string getSolutionName() const { 
        return(results_); 
    }
    virtual bool isSat(const std::vector<std::string>& vec);
    virtual void listOptions(std::ostream& os, const std::string& dir);
    virtual std::string name() const { return(Name()); }
    virtual void setUnique(const std::string& original) {
        tmpFile_ += original;
        results_ += original;
    }

private:
    std::string getTempFile() const { return(tmpFile_); }

private:
    std::string tmpFile_, results_;
};


#endif // JERUSAT1_3_SOLVER_CSE473_H

