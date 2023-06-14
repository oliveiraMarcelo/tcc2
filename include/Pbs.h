// Macro guard
#ifndef PBS_SOLVER_CSE473_H
#define PBS_SOLVER_CSE473_H

// Files included
#include "SolverInterface.h"


/*============================================================================//
    MiniSat.h: header file - implementation of SolverInterface for
     minisat.

    Implementation: Shane J. Neph, Feb 2006, University of Washington
//============================================================================*/

struct PBSSolver : public SolverInterface {
    static std::string ExeName()
        { return("pseudobs"); }

    static std::string Name()
        { return("pseudobs"); }

    PBSSolver() : tmpFile_("pbs.stats"),
                      results_("pbs.results")
        { /* */ }

    virtual ~PBSSolver()
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
        std::string toRtn = exe() + " " + wffFileName;
        /*        toRtn += (" > " + getTempFile()); */
        toRtn += ("  " + getTempFile());
        return(dir + toRtn);
    }
    virtual std::string getExeNameAndArgs(const std::string& dir,
                                          const std::string& wffFileName,
                                          const std::string& options) {
        std::string toRtn = exe() + " " + wffFileName;
        toRtn += (" " + options);
/*        toRtn += (" > " + getTempFile()); */
        toRtn += ("  " + getTempFile());
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
    std::string getTempFile() const {
        return(tmpFile_);
    }

private:
    std::string tmpFile_, results_;
};


#endif // PBS_SOLVER_CSE473_H
