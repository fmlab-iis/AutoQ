/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Copyright (c) 2011  Ondra Lengal <ilengal@fit.vutbr.cz>
 *
 *  Description:
 *    Implementation of miscellaneous utility gadgets.
 *
 *****************************************************************************/

// AUTOQ headers
#include <autoq/autoq.hh>
#include <autoq/util/util.hh>

// Standard library headers
#include <regex>
#include <fstream>
#include <sys/types.h>
#include <sys/wait.h>

/**
 * @brief  Trim whitespaces from a string (both left and right)
 */
std::string AUTOQ::Util::trim(const std::string& str)
{
	std::string result = str;

	// trim from start
	result.erase(result.begin(), std::find_if(result.begin(), result.end(),
		[](int ch) {return !std::isspace(ch);}));

	// trim from end
	result.erase(std::find_if(result.rbegin(), result.rend(),
		[](int ch) {return !std::isspace(ch);}).base(), result.end());

	return result;
}

std::string AUTOQ::Util::ReadFile(const std::string& fileName)
{
	std::ifstream t(fileName);
	if (!t)
	{	// in case the file could not be open
		throw std::runtime_error("[ERROR] Failed to open file " + fileName + ".");
	}

	std::string str;

	t.seekg(0, std::ios::end);
	str.reserve(t.tellg());
	t.seekg(0, std::ios::beg);

	str.assign((std::istreambuf_iterator<char>(t)),
		std::istreambuf_iterator<char>());

	return str;
}

bool AUTOQ::Util::ShellCmd(const std::string &cmd, std::string &result) {
    char buffer[512];
    result = "";

    // Open pipe to file
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        return false;
    }

    // read till end of process:
    while (!feof(pipe)) {
        // use buffer to read and add to result
        if (fgets(buffer, sizeof(buffer), pipe) != NULL)
            result += buffer;
    }

    pclose(pipe);
    return true;
}

// removed due to compilation issue
#if 0
bool AUTOQ::Util::ShellCmd(const std::vector<std::string> &cmd, std::string &result) {
    int pipefd[2];
    if (pipe(pipefd) == -1) {
        std::cerr << "[ERROR] Failed to create pipe." << std::endl;
        return false;
    }

    pid_t pid = fork();
    if (pid == -1) {
        std::cerr << "[ERROR] Failed to fork." << std::endl;
        return false;
    } else if (pid == 0) { // Child process
        close(pipefd[0]); // Close unused read end
        // Redirect standard output to the write end of the pipe
        dup2(pipefd[1], STDOUT_FILENO);

        // Execute the command with the provided arguments
        // const char* args[] = {"ls", "-l", nullptr};  // Replace with your desired arguments
        // Create an array of const char* to hold the converted arguments
        const char** args = new const char*[cmd.size() + 1]; // +1 for the terminating nullptr
        for (size_t i = 0; i < cmd.size(); ++i)
            args[i] = cmd[i].c_str();
        args[cmd.size()] = nullptr; // Terminating nullptr
        // for (size_t i = 0; i < cmd.size(); ++i)
        //     std::cout << "args" << i << ": " << args[i] << "\n";
        execvp(args[0], const_cast<char**>(args));
        // If execvp() fails, this block will be executed
        delete[] args; // Free the array itself
        std::cerr << "[ERROR] Failed to execute command." << std::endl;
        exit(1);
    } else { // Parent process
        close(pipefd[1]); // Close unused write end

        char buffer[256];
        ssize_t bytes, bytesRead;
        while ((bytesRead = read(pipefd[0], buffer, sizeof(buffer))) > 0) {
            // Process and print the data read from the command's output
            // std::cout.write(buffer, bytesRead);
            bytes = bytesRead;
        }
        result = std::string(buffer, bytes); // avoid garbage data due to the lack of initialization

        close(pipefd[0]);
        waitpid(pid, nullptr, 0); // Wait for the child process to finish
    }
    return true;
}
#endif

// AUTOQ::AutBase::StateDict AUTOQ::Util::CreateProductStringToStateMap(
// 	const AUTOQ::AutBase::StateDict& lhsCont,
// 	const AUTOQ::AutBase::StateDict& rhsCont,
// 	const AutBase::ProductTranslMap& translMap)
// {
// 	typedef AUTOQ::AutBase::StateDict StateDict;

// 	StateDict result;

// 	for (auto mapElem : translMap)
// 	{
// 		const auto& key = mapElem.first;

// 		StateDict::ConstIteratorBwd itLhs;
// 		if ((itLhs = lhsCont.FindBwd(key.first)) == lhsCont.EndBwd())
// 		{
// 			assert(false);  // fail gracefully
// 		}

// 		StateDict::ConstIteratorBwd itRhs;
// 		if ((itRhs = rhsCont.FindBwd(key.second)) == rhsCont.EndBwd())
// 		{
// 			assert(false);  // fail gracefully
// 		}

// 		std::string prodStateStr = '[' + itLhs->second + "_1|" +
// 			itRhs->second + "_2]";
// 		result.insert(std::make_pair(prodStateStr, mapElem.second));
// 	}

// 	return result;
// }


// AUTOQ::AutBase::StateDict AUTOQ::Util::CreateUnionStringToStateMap(
// 	const AUTOQ::AutBase::StateDict& lhsCont,
// 	const AUTOQ::AutBase::StateDict& rhsCont,
// 	const AutBase::StateToStateMap* translMapLhs,
// 	const AutBase::StateToStateMap* translMapRhs)
// {
// 	typedef AUTOQ::AutBase::StateType StateType;
// 	typedef AUTOQ::AutBase::StateToStateMap StateToStateMap;
// 	typedef AUTOQ::AutBase::StateDict StateDict;

// 	StateDict result;

// 	for (auto dictElem : lhsCont)
// 	{
// 		StateType state = dictElem.second;
// 		if (translMapLhs != nullptr)
// 		{	// in case there should be translation
// 			StateToStateMap::const_iterator itTransl;
// 			if ((itTransl = translMapLhs->find(state)) == translMapLhs->end())
// 			{
// 				assert(false);    // fail gracefully
// 			}

// 			state = itTransl->second;
// 		}

// 		if (!result.insert(std::make_pair(dictElem.first + "_1", state)).second)
// 		{	// in the case there is already something
// 			assert(false);
// 		}

// 	}

// 	for (auto dictElem : rhsCont)
// 	{
// 		StateType state = dictElem.second;
// 		if (translMapRhs != nullptr)
// 		{	// in case there should be translation
// 			StateToStateMap::const_iterator itTransl;
// 			if ((itTransl = translMapRhs->find(state)) == translMapRhs->end())
// 			{
// 				assert(false);    // fail gracefully
// 			}

// 			state = itTransl->second;
// 		}

// 		if (!result.insert(std::make_pair(dictElem.first + "_2", state)).second)
// 		{	// in the case there is already something
// 			assert(false);
// 		}
// 	}

// 	return result;
// }
