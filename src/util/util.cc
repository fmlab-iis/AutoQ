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
#include "autoq/autoq.hh"
#include "autoq/error.hh"
#include "autoq/util/util.hh"

// Standard library headers
#include <iostream>
#include <sstream>
#include <fstream>
#include <sys/types.h>
#include <sys/wait.h>

std::string AUTOQ::Util::ReadFile(const std::string& fileName)
{
	std::ifstream t(fileName);
	if (!t)
	{	// in case the file could not be open
		THROW_AUTOQ_ERROR("Failed to open file " + fileName + ".");
	}

	std::string str;

	t.seekg(0, std::ios::end);
	str.reserve(t.tellg());
	t.seekg(0, std::ios::beg);

	str.assign((std::istreambuf_iterator<char>(t)),
		std::istreambuf_iterator<char>());

	return str;
}

// const int MAX_ARG_STRLEN = 131070; // in fact is 131072 on the Internet
std::string AUTOQ::Util::ShellCmd(const std::string &cmd) {
    // int length = cmd.length();
    // if (length > MAX_ARG_STRLEN) {
    //     std::vector<std::string> args;
    //     for (int i=0; i<length; i+=MAX_ARG_STRLEN) {
    //         args.push_back(cmd.substr(i, MAX_ARG_STRLEN));
    //     }
    //     return AUTOQ::Util::ShellCmd(args);
    // }

    char buffer[512];
    std::string result = "";

    // Open pipe to file
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        Log::error(cmd);
        THROW_AUTOQ_ERROR("popen() failed!");
    }

    // read till end of process (use fgets result, not feof, to avoid one extra read)
    while (fgets(buffer, sizeof(buffer), pipe) != nullptr) {
        result += buffer;
    }

    pclose(pipe);
    return result;
}

void AUTOQ::Util::Log::info(const std::string& msg) {
    std::cout << msg << std::endl;
}

void AUTOQ::Util::Log::error(const std::string& msg) {
    std::cerr << msg << std::endl;
}

// removed due to compilation issue
#if 0
std::string AUTOQ::Util::ShellCmd(const std::vector<std::string> &cmd) {
    int pipefd[2];
    std::string result = "";

    if (pipe(pipefd) == -1) {
        THROW_AUTOQ_ERROR("popen() failed!");
    }

    pid_t pid = fork();
    if (pid == -1) {
        THROW_AUTOQ_ERROR("fork() failed!");
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
        Log::error("[ERROR] Failed to execute command.");
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
    return result;
}
#endif
