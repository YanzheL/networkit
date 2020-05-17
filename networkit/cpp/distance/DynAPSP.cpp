/*
 * DynAPSP.cpp
 *
 *  Created on: 12.08.2015
 *      Author: Arie Slobbe, Elisabetta Bergamini
 */

#include <algorithm>
#include <ctime>
#include <memory>
#include <queue>
#include <unordered_set>

#include <networkit/auxiliary/Log.hpp>
#include <networkit/auxiliary/NumericTools.hpp>
#include <networkit/auxiliary/PrioQueue.hpp>
#include <networkit/distance/APSP.hpp>
#include <networkit/distance/BFS.hpp>
#include <networkit/distance/Dijkstra.hpp>
#include <networkit/distance/DynAPSP.hpp>
#include <networkit/distance/SSSP.hpp>

namespace NetworKit {

DynAPSP::DynAPSP(Graph &G) : APSP(G) {}

/**
 * Run method that stores a single shortest path for each node pair and stores shortest distances
 */
void DynAPSP::run() {
    distances.resize(G.upperNodeIdBound());
    G.parallelForNodes([&](node u) {
        std::unique_ptr<SSSP> sssp;
        if (G.isWeighted()) {
            sssp.reset(new Dijkstra(G, u));
        } else {
            sssp.reset(new BFS(G, u));
        }
        sssp->run();
        auto res = sssp->getDistances();
        std::copy(res.begin(), res.end(), distances.begin() + u * G.upperNodeIdBound());
    });
    hasRun = true;
}

std::vector<node> DynAPSP::getPath(node u, node v) {
    std::vector<node> path = {};
    count n = G.upperNodeIdBound();
    if (distances[u * n + v] < std::numeric_limits<edgeweight>::max()) {
        node current = v;
        while (current != u) {
            path.push_back(current);
            G.forInEdgesOf(current, [&](node z, edgeweight w) {
                if (distances[u * n + current] == distances[u * n + z] + w) {
                    current = z;
                }
            });
        }
        path.push_back(u);
        std::reverse(path.begin(), path.end());
    }
    return path;
}

void DynAPSP::update(GraphEvent event) {
    visitedPairs = 0;
    INFO("Entering update");
    node u = event.u;
    node v = event.v;
    edgeweight weightuv = G.weight(u, v);
    if (!(event.type == GraphEvent::EDGE_ADDITION
          || (event.type == GraphEvent::EDGE_WEIGHT_INCREMENT && event.w < 0))) {
        throw std::runtime_error(
            "event type not allowed. Edge insertions and edge weight decreases only.");
    }
    count upper_node_id_bound = G.upperNodeIdBound();
    if (weightuv < distances[u * upper_node_id_bound + v]) {
        // initializations
        std::vector<node> source_nodes(upper_node_id_bound);
        std::vector<node> n_sources(upper_node_id_bound, 0);
        std::queue<node> Q;
        std::vector<bool> enqueued(G.upperNodeIdBound(), false);
        // phase 1: find affected source nodes using bfs
        count i = 0;
        std::queue<node> bfsQ;
        std::vector<bool> visited(upper_node_id_bound, false);
        INFO("Phase 1. distances[", u, "][", v, "] = ", distances[u * upper_node_id_bound + v],
             ", and G.weight", u, ", ", v, " = ", G.weight(u, v));
        distances[u * upper_node_id_bound + v] = weightuv;
        if (!G.isDirected()) {
            distances[v * upper_node_id_bound + u] = distances[u * upper_node_id_bound + v];
        }
        bfsQ.push(u);
        INFO("Entering bfs");
        while (!bfsQ.empty()) {
            node x = bfsQ.front();
            bfsQ.pop();
            DEBUG("Dequeueing node ", x);
            G.forInNeighborsOf(x, [&](node w, edgeweight) { // identify and process neighbors w of x
                if (visited[w] == false
                    && distances[w * upper_node_id_bound + v]
                           > distances[w * upper_node_id_bound + u] + weightuv) {
                    bfsQ.push(w);
                    DEBUG("Pushing neighbor ", w);
                    visited[w] = true;
                    source_nodes[i] = w;
                    i++;
                }
            });
        }
        // notice that source nodes does not contain u
        n_sources[u] = i;
        // phase 2: for all source nodes, update distances to affected sinks
        std::vector<node> Pred(G.upperNodeIdBound());
        Pred[v] = u;
        std::stack<node> stack;
        stack.push(v);
        visited.clear();
        visited.resize(upper_node_id_bound, false);
        while (!stack.empty()) {
            node y = stack.top();
            if (!visited[y]) {
                // we leave y in the stack (so that we know when we're done visiting the subtree
                // rooted in y)
                n_sources[y] = n_sources[Pred[y]];
                visited[y] = true;
                for (count c = 0; c < n_sources[y]; c++) {
                    node s = source_nodes[c];
                    if (distances[s * upper_node_id_bound + y]
                        > distances[s * upper_node_id_bound + u] + weightuv
                              + distances[v * upper_node_id_bound + y]) {
                        distances[s * upper_node_id_bound + y] =
                            distances[s * upper_node_id_bound + u] + weightuv
                            + distances[v * upper_node_id_bound + y];
                        if (!G.isDirected()) {
                            distances[y * upper_node_id_bound + s] =
                                distances[s * upper_node_id_bound + y];
                        }
                    } else {
                        std::swap(source_nodes[c], source_nodes[n_sources[y] - 1]);
                        c--;
                        n_sources[y]--;
                    }
                }
                // adding successors of y to the stack
                G.forNeighborsOf(y, [&](node w, edgeweight weightyw) {
                    // we go down the BFS tree rooted in v in a DFS order (the last check is
                    // necessary to make sure that (y, w) is an edge of the BFS tree rooted in v)
                    if (visited[w] == false
                        && distances[u * upper_node_id_bound + w]
                               > distances[v * upper_node_id_bound + w] + weightuv
                        && distances[v * upper_node_id_bound + w]
                               == distances[v * upper_node_id_bound + y] + weightyw) {
                        distances[u * upper_node_id_bound + w] =
                            distances[v * upper_node_id_bound + w] + weightuv;
                        if (!G.isDirected()) {
                            distances[w * upper_node_id_bound + u] =
                                distances[u * upper_node_id_bound + w];
                        }
                        stack.push(w);
                        Pred[w] = y;
                    }
                });
            } else {
                // we remove y from the stack
                stack.pop();
            }
        }
        // while(!Q.empty()) {
        // 	node y = getMin();
        // 	enqueued[y] = false;
        // 	// update for all source nodes
        // 	for (node x: source_nodes[Pred[y]]) {
        // 		visitedPairs ++;
        // 		if (distances[x][y] > distances[x][u] + distances[u][y]) {
        // 			distances[x][y] = distances[x][u] + distances[u][y];
        // 			if(!G.isDirected()) {
        // 				distances[y][x] = distances[x][y];
        // 			}
        // 			source_nodes[y].push_back(x);
        // 		}
        // 	}
        //
        // 	G.forNeighborsOf(y, [&](node w, edgeweight weightyw){
        // 		if (distances[u][w] > distances[u][y] + weightyw && distances[v][w] ==
        // distances[v][y]
        // + weightyw) { // I also check that y was a predecessor for w in the s.p. from v
        // 			distances[u][w] = distances[u][y] + weightyw;
        // 			Pred[w] = y;
        // 			if(!G.isDirected()) {
        // 				distances[w][u] = distances[u][w];
        // 			}
        // 			updateQueue(w, distances[u][w]);
        // 		}
        // 	});
        // }
    }
}

void DynAPSP::updateBatch(const std::vector<GraphEvent> &batch) {
    for (auto e : batch) {
        update(e);
    }
}

count DynAPSP::visPairs() {
    return visitedPairs;
}

} /* namespace NetworKit */
