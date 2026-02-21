// Included inside struct EvaluationVisitor { ... } — helper used by visitTset/visitSet.

    perm_t sortedConnectedComponent(const graph_t &edges) {
        std::map<int, std::vector<int>> graph;
        std::set<int> unvisited;
        // Build the undirected graph
        for (const auto& [u, v] : edges) {
            graph[u].push_back(v);
            graph[v].push_back(u);
            unvisited.insert(u);
            unvisited.insert(v);
        }
        // BFS to collect all reachable nodes from 'start'
        perm_t result;
        while (!unvisited.empty()) {
            std::set<int> visited;
            int start = *unvisited.begin();
            std::queue<int> q;
            q.push(start);
            visited.insert(start);
            unvisited.erase(start);
            while (!q.empty()) {
                int node = q.front(); q.pop();
                for (int neighbor : graph[node]) {
                    if (visited.count(neighbor) == 0) {
                        visited.insert(neighbor);
                        q.push(neighbor);
                    }
                }
            }
            // Copy to a vector and sort
            std::vector<int> cc(visited.begin(), visited.end());
            std::sort(cc.begin(), cc.end());
            result.insert(cc);
        }
        return result;
    }
