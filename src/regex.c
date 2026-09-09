#include "regex.h"

#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef enum
{
    TRANSITION_NONE,
    TRANSITION_LITERAL,
    TRANSITION_WILDCARD,
    TRANSITION_EPSILON
} TransitionType;

typedef struct
{
    uint16_t from_state;
    uint16_t to_state;
    TransitionType type;
    char literal;
} Edge;

typedef struct
{
    uint16_t start_state;
    uint16_t accept_state;
    uint16_t state_count;
    Edge *edges;
    uint16_t edge_count;
} NFA;

uint64_t activateState(uint64_t activeStates, uint8_t s)
{
    return activeStates | (UINT64_C(1) << s);
}

uint64_t deactivateState(uint64_t activeStates, uint8_t s)
{
    return activeStates & ~(UINT64_C(1) << s);
}

bool isActiveState(uint64_t activeStates, uint8_t s)
{
    return (activeStates & (UINT64_C(1) << s)) != 0;
}

Edge emptyEdge(void)
{
    Edge e;
    e.from_state = 0;
    e.to_state = 0;
    e.literal = '\0';
    e.type = TRANSITION_NONE;
    return e;
}

NFA emptyNFA(void)
{
    NFA n;
    n.start_state = 0;
    n.accept_state = 0;
    n.state_count = 1;
    n.edges = NULL;
    n.edge_count = 0;
    return n;
}

NFA addEdge(NFA n, uint16_t from_state, uint16_t to_state, TransitionType type, char rule)
{
    uint16_t largestState = from_state > to_state ? from_state : to_state;
    if (largestState >= 64)
    {
        fprintf(stderr, "State index exceeds bitset capacity\n");
        free(n.edges);
        exit(EXIT_FAILURE);
    }

    if (largestState >= n.state_count)
        n.state_count = largestState + 1;

    Edge e = emptyEdge();
    e.from_state = from_state;
    e.to_state = to_state;
    e.type = type;
    e.literal = (type == TRANSITION_LITERAL) ? rule : '\0';

    Edge *resized = realloc(n.edges, (n.edge_count + 1) * sizeof(Edge));
    if (resized == NULL)
    {
        fprintf(stderr, "Memory allocation failed\n");
        free(n.edges);
        exit(EXIT_FAILURE);
    }

    n.edges = resized;
    n.edges[n.edge_count] = e;
    n.edge_count++;

    return n;
}

NFA addLiteral(char literal)
{
    // create empty NFA fragment
    NFA fragment = emptyNFA();

    // add edge with literal rule
    fragment = addEdge(fragment, 0, 1, TRANSITION_LITERAL, literal);

    // set edge to_state as NFA accept state
    fragment.accept_state = 1;

    // return NFA fragment
    return fragment;
}

NFA addWildcard(void)
{
    // create empty NFA fragment
    NFA fragment = emptyNFA();

    // add edge with epsilon transition
    fragment = addEdge(fragment, 0, 1, TRANSITION_WILDCARD, '\0');

    // set edge to_state as NFA accept state
    fragment.accept_state = 1;

    // return NFA fragment
    return fragment;
}

NFA addKleeneClosure(NFA fragment)
{
    if (fragment.state_count >= 64)
    {
        fprintf(stderr, "NFA is too large\n");
        free(fragment.edges);
        exit(EXIT_FAILURE);
    }

    // store new state numbers
    uint16_t oldStart = fragment.start_state + 1;
    uint16_t oldAccept = fragment.accept_state + 1;
    uint16_t newAccept = fragment.state_count + 1;

    // set new state numbers to fit the new first state
    fragment.start_state = 0;
    fragment.accept_state = newAccept;
    fragment.state_count += 2;
    for (size_t i = 0; i < fragment.edge_count; i++)
    {
        fragment.edges[i].from_state++;
        fragment.edges[i].to_state++;
    }

    // add epsilon transitions following thompsons construction algorithm
    fragment = addEdge(fragment, 0, oldStart, TRANSITION_EPSILON, '\0');
    fragment = addEdge(fragment, 0, newAccept, TRANSITION_EPSILON, '\0');
    fragment = addEdge(fragment, oldAccept, oldStart, TRANSITION_EPSILON, '\0');
    fragment = addEdge(fragment, oldAccept, newAccept, TRANSITION_EPSILON, '\0');

    // return altered NFA fragment
    return fragment;
}

NFA addKleenePlus(NFA fragment)
{
    if (fragment.state_count >= 64)
    {
        fprintf(stderr, "NFA is too large\n");
        free(fragment.edges);
        exit(EXIT_FAILURE);
    }

    fragment = addEdge(fragment, fragment.accept_state, fragment.start_state, TRANSITION_EPSILON, '\0');
    fragment = addEdge(fragment, fragment.accept_state, fragment.state_count, TRANSITION_EPSILON, '\0');
    fragment.accept_state = fragment.state_count - 1;

    return fragment;
}

NFA concatenate(NFA left, NFA right)
{
    if (left.edge_count == 0)
        return right;

    if (right.edge_count == 0)
        return left;

    if (left.state_count + right.state_count > 64)
    {
        fprintf(stderr, "Concatenated NFA is too large\n");
        free(left.edges);
        free(right.edges);
        exit(EXIT_FAILURE);
    }

    // store original left edge count and final edge count
    uint16_t oldLeftEdgeCount = left.edge_count;
    uint16_t finalEdgeCount = left.edge_count + right.edge_count + 1;

    // shift all states in right by left state count
    right.start_state += left.state_count;
    right.accept_state += left.state_count;
    for (size_t i = 0; i < right.edge_count; i++)
    {
        right.edges[i].from_state += left.state_count;
        right.edges[i].to_state += left.state_count;
    }

    // realloc left edges to fit all left and right edges + connecting epsilon transition
    Edge *resized = realloc(left.edges, finalEdgeCount * sizeof(Edge));
    if (resized == NULL)
    {
        fprintf(stderr, "Memory allocation failed\n");
        free(left.edges);
        free(right.edges);
        exit(EXIT_FAILURE);
    }
    left.edges = resized;

    // create epsilon transition from left accept to right start
    Edge connection = emptyEdge();
    connection.from_state = left.accept_state;
    connection.to_state = right.start_state;
    connection.type = TRANSITION_EPSILON;
    left.edges[oldLeftEdgeCount] = connection;

    // copy shifted edges from right to left
    left.edge_count = finalEdgeCount;
    for (size_t i = 0; i < right.edge_count; i++)
        left.edges[oldLeftEdgeCount + 1 + i] = right.edges[i];

    // set left accept state to right accept
    left.accept_state = right.accept_state;

    // add state counts together
    left.state_count += right.state_count;

    // free allocated memory and return left NFA
    free(right.edges);
    return left;
}

typedef enum
{
    TOKEN_LITERAL,
    TOKEN_WILDCARD,
    TOKEN_STAR,
    TOKEN_PLUS,
    TOKEN_ALTERNATION,
    TOKEN_GROUP_OPEN,
    TOKEN_GROUP_CLOSE
} RegexTokenType;

typedef struct
{
    RegexTokenType type;
    char literal;
    uint16_t depth;
    uint16_t group_id;
} RegexToken;

static RegexToken *tokenizeRegex(const char *pattern, size_t *token_count)
{
    // allocate one token per possible pattern character and a stack for nested groups
    size_t pattern_length = strlen(pattern);
    RegexToken *tokens = calloc(pattern_length, sizeof(*tokens));
    uint16_t *group_stack = calloc(pattern_length + 1, sizeof(*group_stack));

    // initialize tokenizer position and group tracking
    uint16_t depth = 0;
    uint16_t next_group_id = 1;
    size_t count = 0;

    // return failure if allocation failed
    if ((pattern_length > 0 && tokens == NULL) || group_stack == NULL)
    {
        free(tokens);
        free(group_stack);
        return NULL;
    }

    for (size_t i = 0; i < pattern_length; i++)
    {
        // treat each character as a literal unless recognized as syntax
        RegexToken token = {
            .type = TOKEN_LITERAL,
            .literal = pattern[i],
            .depth = depth,
            .group_id = group_stack[depth]};

        // consume the character after a backslash as an escaped literal
        if (pattern[i] == '\\' && i + 1 < pattern_length)
        {
            token.literal = pattern[++i];
        }
        // enter a new group and assign it an ID distinct from sibling groups
        else if (pattern[i] == '(')
        {
            if (depth == UINT16_MAX || next_group_id == UINT16_MAX)
                goto invalid_pattern;

            depth++;
            group_stack[depth] = next_group_id++;
            token.type = TOKEN_GROUP_OPEN;
            token.depth = depth;
            token.group_id = group_stack[depth];
            token.literal = '\0';
        }
        // close the current group and restore its parent as the active group
        else if (pattern[i] == ')')
        {
            if (depth == 0)
                goto invalid_pattern;

            token.type = TOKEN_GROUP_CLOSE;
            token.group_id = group_stack[depth];
            token.literal = '\0';
            depth--;
        }
        // classify supported regular expression operators
        else if (pattern[i] == '.')
        {
            token.type = TOKEN_WILDCARD;
            token.literal = '\0';
        }
        else if (pattern[i] == '*')
        {
            token.type = TOKEN_STAR;
            token.literal = '\0';
        }
        else if (pattern[i] == '+')
        {
            token.type = TOKEN_PLUS;
            token.literal = '\0';
        }
        else if (pattern[i] == '|')
        {
            token.type = TOKEN_ALTERNATION;
            token.literal = '\0';
        }

        // append the completed token while preserving pattern order
        tokens[count++] = token;
    }

    // reject a pattern with one or more unclosed groups
    if (depth != 0)
        goto invalid_pattern;

    // return the completed token array and its populated length
    free(group_stack);
    *token_count = count;
    return tokens;

invalid_pattern:
    // free partial tokenizer state and report failure
    free(tokens);
    free(group_stack);
    *token_count = 0;
    return NULL;
}

NFA regexToNFA(const char *p)
{
    NFA n = emptyNFA();

    size_t token_count = 0;
    RegexToken *tokens = tokenizeRegex(p, &token_count);
    if (tokens == NULL && p[0] != '\0')
    {
        fprintf(stderr, "Invalid regular expression\n");
        return n;
    }

    for (size_t i = 0; i < token_count; i++)
    {
        RegexToken token = tokens[i];
        NFA fragment;

        switch (token.type)
        {
        case TOKEN_LITERAL:
            fragment = addLiteral(token.literal);
            break;

        case TOKEN_WILDCARD:
            fragment = addWildcard();
            break;

        default:
            continue;
        }

        if (i + 1 < token_count && tokens[i + 1].type == TOKEN_STAR)
        {
            fragment = addKleeneClosure(fragment);
            i++;
        }
        else if (i + 1 < token_count && tokens[i + 1].type == TOKEN_PLUS)
        {
            fragment = addKleenePlus(fragment);
            i++;
        }

        n = concatenate(n, fragment);
    }

    // still missing parser before complex expressions are possible

    free(tokens);
    return n;
}

uint64_t simulateEpsilonTransitions(uint64_t active_states, NFA n)
{
    uint64_t previous;
    do
    {
        previous = active_states;
        for (size_t i = 0; i < n.edge_count; i++)
            if (n.edges[i].type == TRANSITION_EPSILON && isActiveState(active_states, n.edges[i].from_state))
                active_states = activateState(active_states, n.edges[i].to_state);
    } while (active_states != previous);
    return active_states;
}

uint64_t simulateNonEpsilonTransitions(uint64_t active_states, NFA n, char c)
{
    uint64_t result_states = 0;
    for (size_t i = 0; i < n.edge_count; i++)
    {
        bool matches =
            n.edges[i].type == TRANSITION_WILDCARD ||
            (n.edges[i].type == TRANSITION_LITERAL && n.edges[i].literal == c);

        if (matches && isActiveState(active_states, n.edges[i].from_state))
            result_states = activateState(result_states, n.edges[i].to_state);
    }
    return result_states;
}

bool contains_regex(const char *string, const char *pattern)
{
    NFA n = addKleeneClosure(addWildcard());
    n = concatenate(n, regexToNFA(pattern));
    n = concatenate(n, addKleeneClosure(addWildcard()));

    // define active states for NFA n
    uint64_t active_states = 0;
    active_states = activateState(active_states, n.start_state);

    // simulate initial epsilon transitions on n
    active_states = simulateEpsilonTransitions(active_states, n);

    // loop simulation across string s
    size_t string_len = strlen(string);
    for (size_t i = 0; i < string_len; i++)
    {
        // simulate transitions on n
        active_states = simulateNonEpsilonTransitions(active_states, n, string[i]);
        active_states = simulateEpsilonTransitions(active_states, n);
    }

    // return true if accepting state is active
    bool matched = isActiveState(active_states, n.accept_state);
    free(n.edges);
    return matched;
}
