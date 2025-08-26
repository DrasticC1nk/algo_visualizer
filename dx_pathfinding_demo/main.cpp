#ifndef NOMINMAX
#define NOMINMAX
#endif

#define WIN32_LEAN_AND_MEAN

#include <windows.h>
#include <windowsx.h>
#include <d3d11.h>
#include <d3dcompiler.h>
#include <dxgi.h>
#include <wrl/client.h>

#include <stack>
#include <vector>
#include <queue>
#include <limits>
#include <cassert>
#include <cstdint>
#include <functional>
#include <algorithm>
#include <cmath>
#include <random>
#include <string>

#pragma comment(lib, "d3d11.lib")
#pragma comment(lib, "d3dcompiler.lib")

using Microsoft::WRL::ComPtr;
using namespace std;

static const int GRID_W = 129;
static const int GRID_H = 129;

static const int EXPANSIONS_PER_FRAME = 5;

static const int COST_STRAIGHT = 10;
static const int COST_DIAGONAL = 14;

static const uint32_t COL_EMPTY = 0xffffff; //WHITE
static const uint32_t COL_WALL = 0xFF0A0A0A; //NEAR BLACK
static const uint32_t COL_START = 0xFF2ECC71; //GREEN
static const uint32_t COL_END = 0xFFE74C3C;   //RED
static const uint32_t COL_PATH = 0xFFF1C40F;  //YELLOW
static const uint32_t COL_CUR_PATH = 0xFFADFF2F; //GREEN YELLOW
static const uint32_t COL_VIS_START = 0xFF3498DB; //BLUEISH
static const uint32_t COL_VIS_END = 0xFF1F3C88; //DEEP BLUE
static const uint32_t COL_OPEN_BASE = 0xFF9B59B6; //PURPLE
static const uint32_t COL_OPEN_START = 0xFFE040FB; //BRIGHT PURPLE
static const uint32_t COL_OPEN_END = 0xFF8338EC;   //DEEP PURPLE
static const uint32_t COL_CURRENT_NODE = 0xFFFFFFFF; //WHITE

struct Cell
{
    bool wall = false;
    bool path = false;
    bool visited = false;
    bool open = false;
    bool isCurrentPath = false;
    int distFromStart = 0;
};

struct WallChange
{
    int x, y;
    bool prevState;
};

enum class SearchAlgorithm
{
    Dijkstra,
    AStar
};

struct SearchStats
{
    int nodesVisited = 0;
    int pathLength = 0;
};

static HWND g_hwnd = nullptr;
static SearchStats g_stats;
static vector<vector<WallChange>> g_wallHistory;
static Cell g_grid[GRID_H][GRID_W];
static bool g_haveStart = false, g_haveEnd = false;
static POINT g_start = { -1, -1 };
static POINT g_end = { -1, -1 };
static UINT g_winW = 1024;
static UINT g_winH = 768;
static bool g_mouseRDown = false;
static const DWORD UPDATE_INTERVAL_MS = 25;
static DWORD g_lastUpdateTime = 0;
static const DWORD PATH_ANIM_INTERVAL_MS = 10;
static vector<int> g_finalPathNodes;
static int g_pathAnimIndex = -1;
static UINT g_gridLineVertCount = 0;
static int g_searchTarget = -1;
static const int INF_DIST = numeric_limits<int>::max() / 4;
static int g_maxDist = 0;
static POINT g_lastExpandedNode = { -1, -1 };
static bool g_showHeatmap = false;
static SearchAlgorithm g_currentAlgorithm = SearchAlgorithm::Dijkstra;
static bool g_allowDiagonals = false;
static bool g_useWeightedCosts = false; 

static vector<int> g_dist;
static vector<int> g_prev;
static priority_queue<pair<int, int>, vector<pair<int, int>>, greater<>> g_pq;

static bool g_searchRunning = false;

static ComPtr<ID3D11Device> g_device;
static ComPtr<ID3D11DeviceContext> g_ctx;
static ComPtr<IDXGISwapChain> g_swap;
static ComPtr<ID3D11RenderTargetView> g_rtv;
static ComPtr<ID3D11Texture2D> g_gridTex;
static ComPtr<ID3D11ShaderResourceView> g_gridSRV;
static ComPtr<ID3D11Buffer> g_vb;
static ComPtr<ID3D11InputLayout> g_il;
static ComPtr<ID3D11VertexShader> g_vs;
static ComPtr<ID3D11PixelShader> g_ps;
static ComPtr<ID3D11VertexShader> g_vsLines;
static ComPtr<ID3D11PixelShader> g_psLines;
static ComPtr<ID3D11InputLayout> g_ilLines;
static ComPtr<ID3D11Buffer> g_gridLineVB;

static D3D11_VIEWPORT g_vp;

struct LineVtx
{
    float x, y;
};
struct Vtx
{
    float x, y, z; float u, v;
};

static const Vtx QUAD[6] =
{
    {-1,-1,0,0,1},{-1,1,0,0,0},{1,1,0,1,0},
    {-1,-1,0,0,1},{1,1,0,1,0},{1,-1,0,1,1},
};

static const char* VS_SRC = R"(
    struct VSIn 
    { 
        float3 pos : POSITION; 
        float2 uv : TEXCOORD0; 
    };

    struct VSOut 
    { 
        float4 pos : SV_Position; 
        float2 uv : TEXCOORD0; 
    };

    VSOut main(VSIn vin)
    { 
        VSOut o; 
        o.pos=float4(vin.pos,1); 
        o.uv=vin.uv; return o;
    }
)";

static const char* PS_SRC = R"(
    Texture2D gridTex : register(t0);

    SamplerState samp0 : register(s0);

    struct PSIn 
    { 
        float4 pos:SV_Position; 
        float2 uv:TEXCOORD0; 
    };

    float4 main(PSIn pin) : SV_Target 
    {
        return gridTex.Sample(samp0, pin.uv); 
    }
)";

static const char* VS_LINES = R"(
    struct VSIn 
    { 
        float2 pos : POSITION; 
    };

    struct VSOut 
    { 
        float4 pos : SV_Position; 
    };

    VSOut main(VSIn i)
    { 
        VSOut o; 
        o.pos = float4(i.pos, 0.0, 1.0); 
        return o;
    }
)";

static const char* PS_LINES = R"(
    float4 main() : SV_Target 
    { 
        return float4(0.75,0.75,0.75,1.0); 
    }
)";

void UpdateWindowTitle();

void ClearGrid(bool keepWalls = false)
{
    for (int y = 0; y < GRID_H; ++y)
    {
        for (int x = 0; x < GRID_W; ++x)
        {
            g_grid[y][x].path = false;
            g_grid[y][x].visited = false;
            g_grid[y][x].open = false;
            g_grid[y][x].distFromStart = 0;

            if (!keepWalls)
            {
                g_grid[y][x].wall = false;
            }
        }
    }
    if (!keepWalls)
    {
        g_haveStart = false; g_haveEnd = false;
        g_start = { -1,-1 }; g_end = { -1,-1 };
    }

    g_finalPathNodes.clear();
    g_pathAnimIndex = -1;

    g_stats = {};

    UpdateWindowTitle();
}

inline bool InBounds(int x, int y)
{
    return x >= 0 && y >= 0 && x < GRID_W && y < GRID_H;
}
inline int Idx(int x, int y)
{
    return y * GRID_W + x;
}

void GenerateMaze_RecursiveBacktracker()
{
    ClearGrid(false);

    g_searchRunning = false;
    g_wallHistory.clear();
    g_finalPathNodes.clear();
    g_pathAnimIndex = -1;

    for (int y = 0; y < GRID_H; ++y)
    {
        for (int x = 0; x < GRID_W; ++x)
        {
            g_grid[y][x].wall = true;
        }
    }

    const int MAZE_W = GRID_W - 1;
    const int MAZE_H = GRID_H - 1;

    static mt19937 rng(random_device{}());

    vector<vector<bool>> visited(GRID_H, vector<bool>(GRID_W, false));
    stack<POINT> stack;

    POINT startPos = { 1, 1 };

    visited[startPos.y][startPos.x] = true;
    g_grid[startPos.y][startPos.x].wall = false;

    stack.push(startPos);

    while (!stack.empty())
    {
        POINT current = stack.top();

        vector<POINT> neighbors;

        const int dx[] = { 0, 0, 2, -2 };
        const int dy[] = { 2, -2, 0, 0 };

        for (int i = 0; i < 4; ++i)
        {
            int nx = current.x + dx[i];
            int ny = current.y + dy[i];

            if (nx > 0 && nx < MAZE_W && ny > 0 && ny < MAZE_H && !visited[ny][nx])
            {
                neighbors.push_back({ nx, ny });
            }
        }

        if (!neighbors.empty())
        {
            uniform_int_distribution<int> dist(0, neighbors.size() - 1);

            POINT next = neighbors[dist(rng)];

            int wallX = current.x + (next.x - current.x) / 2;
            int wallY = current.y + (next.y - current.y) / 2;

            g_grid[wallY][wallX].wall = false;
            visited[next.y][next.x] = true;
            g_grid[next.y][next.x].wall = false;


            stack.push(next);
        }
        else
        {
            stack.pop();
        }
    }
}

int Heuristic(int x1, int y1, int x2, int y2)
{
    int dx = abs(x1 - x2);
    int dy = abs(y1 - y2);

    if (g_useWeightedCosts)
    {
        if (g_allowDiagonals)
        {
            return COST_DIAGONAL * min(dx, dy) + COST_STRAIGHT * (max(dx, dy) - min(dx, dy));
        }
        else
        {
            return COST_STRAIGHT * (dx + dy);
        }
    }
    else
    {
        if (g_allowDiagonals)
        {
            return max(dx, dy);
        }
        else
        {
            return dx + dy;
        }
    }
}

void InitSearchAnimated()
{
    g_stats = {};

    UpdateWindowTitle();

    int N = GRID_W * GRID_H;

    g_dist.assign(N, INF_DIST);
    g_prev.assign(N, -1);

    while (!g_pq.empty())
    {
        g_pq.pop();
    }

    int s = Idx(g_start.x, g_start.y);

    g_dist[s] = 0;

    if (g_currentAlgorithm == SearchAlgorithm::AStar)
    {
        int h = Heuristic(g_start.x, g_start.y, g_end.x, g_end.y);

        g_pq.push({ 0 + h, s });
    }
    else
    {
        g_pq.push({ 0, s });
    }

    g_finalPathNodes.clear();
    g_pathAnimIndex = -1;

    for (int y = 0; y < GRID_H; ++y) for (int x = 0; x < GRID_W; ++x)
    {
        g_grid[y][x].visited = false;
        g_grid[y][x].open = false;
        g_grid[y][x].path = false;
        g_grid[y][x].distFromStart = 0;
    }

    g_grid[g_start.y][g_start.x].open = true;
    g_searchTarget = Idx(g_end.x, g_end.y);
    g_searchRunning = true;
    g_maxDist = 0;
}


void TraceCurrentPath()
{
    for (int y = 0; y < GRID_H; ++y)
    {
        for (int x = 0; x < GRID_W; ++x)
        {
            g_grid[y][x].isCurrentPath = false;
        }
    }

    if (!g_searchRunning || g_lastExpandedNode.x == -1)
    {
        return;
    }

    int cur = Idx(g_lastExpandedNode.x, g_lastExpandedNode.y);

    const int s = Idx(g_start.x, g_start.y);

    while (cur != -1 && cur != s)
    {
        int x = cur % GRID_W;
        int y = cur / GRID_W;

        g_grid[y][x].isCurrentPath = true;

        cur = g_prev[cur];
    }
}

bool StepSearchAnimated(int maxExpansions)
{
    if (!g_searchRunning)
    {
        g_lastExpandedNode = { -1, -1 };

        return true;
    }

    const int OFFS[8][2] = 
    {
        {1,0}, {-1,0}, {0,1}, {0,-1},
        {1,1}, {1,-1}, {-1,1}, {-1,-1}
    };

    int expansions = 0;

    bool needsTitleUpdate = false;

    while (expansions < maxExpansions && !g_pq.empty())
    {
        auto top = g_pq.top(); g_pq.pop();

        int u = top.second;

        int ux = u % GRID_W, uy = u / GRID_W;

        if (g_grid[uy][ux].visited)
        {
            continue;
        }

        g_stats.nodesVisited++;

        needsTitleUpdate = true;

        g_lastExpandedNode = { ux, uy };
        g_grid[uy][ux].visited = true;
        g_grid[uy][ux].open = false;
        g_grid[uy][ux].distFromStart = g_dist[u];
        g_maxDist = max(g_maxDist, g_dist[u]);

        if (u == g_searchTarget)
        {
            g_searchRunning = false;
            g_lastExpandedNode = { -1, -1 };
            g_finalPathNodes.clear();

            int cur = u, s = Idx(g_start.x, g_start.y);

            while (cur != -1 && cur != s)
            {
                g_finalPathNodes.push_back(cur);

                cur = g_prev[cur];
            }
            if (!g_finalPathNodes.empty())
            {
                g_pathAnimIndex = g_finalPathNodes.size() - 1;

                g_stats.pathLength = g_finalPathNodes.size();
            }

            UpdateWindowTitle();

            return true;
        }

        for (int i = 0; i < (g_allowDiagonals ? 8 : 4); ++i)
        {
            int nx = ux + OFFS[i][0];
            int ny = uy + OFFS[i][1];

            if (!InBounds(nx, ny) || g_grid[ny][nx].wall)
            {
                continue;
            }

            if (i >= 4)
            {
                if (g_grid[uy][ux + OFFS[i][0]].wall && g_grid[uy + OFFS[i][1]][ux].wall)
                {
                    continue;
                }
            }

            int cost;

            if (g_useWeightedCosts)
            {
                cost = (i < 4) ? COST_STRAIGHT : COST_DIAGONAL;
            }
            else
            {
                cost = 1;
            }

            int v = Idx(nx, ny);
            int alt = g_dist[u] + cost;

            if (alt < g_dist[v])
            {
                g_dist[v] = alt;
                g_prev[v] = u;

                if (g_currentAlgorithm == SearchAlgorithm::AStar)
                {
                    int h = Heuristic(nx, ny, g_end.x, g_end.y);
                    g_pq.push({ alt + h, v });
                }
                else
                {
                    g_pq.push({ alt, v });
                }

                g_grid[ny][nx].open = true;
            }
        }

        ++expansions;
    }

    if (needsTitleUpdate)
    {
        UpdateWindowTitle();
    }

    if (g_pq.empty())
    {
        g_searchRunning = false;
        g_lastExpandedNode = { -1, -1 };

        UpdateWindowTitle();
    }

    return !g_searchRunning;
}


void StartOrRestartSearch()
{
    if (g_haveStart && g_haveEnd)
    {
        if (g_start.x == g_end.x && g_start.y == g_end.y)
        {
            for (int y = 0; y < GRID_H; ++y) for (int x = 0; x < GRID_W; ++x)
            {
                g_grid[y][x].visited = false; g_grid[y][x].open = false; g_grid[y][x].path = false;
            }

            g_grid[g_start.y][g_start.x].path = true;
            g_searchRunning = false;

            g_stats = {};
            g_stats.pathLength = 0;

            UpdateWindowTitle();

            return;
        }

        InitSearchAnimated();
    }
    else
    {
        g_searchRunning = false;
    }
}

void UpdateGridTexture()
{
    if (!g_gridTex)
    {
        return;
    }

    D3D11_MAPPED_SUBRESOURCE m{};

    if (SUCCEEDED(g_ctx->Map(g_gridTex.Get(), 0, D3D11_MAP_WRITE_DISCARD, 0, &m)))
    {
        uint8_t* dst = (uint8_t*)m.pData;

        for (int y = 0; y < GRID_H; ++y)
        {
            uint32_t* row = (uint32_t*)(dst + y * m.RowPitch);

            for (int x = 0; x < GRID_W; ++x)
            {
                uint32_t col = COL_EMPTY;

                Cell& c = g_grid[y][x];

                if (c.wall)
                {
                    col = COL_WALL;
                }
                else if (c.path)
                {
                    float cost_normalizer = g_useWeightedCosts ? (float)COST_STRAIGHT : 1.0f;
                    float normalized_dist = c.distFromStart / cost_normalizer;
                    float pulse = (sinf(GetTickCount64() / 150.0f - normalized_dist * 0.2f) + 1.0f) * 0.5f;

                    float scale = 0.7f + 0.8f * pulse;

                    uint8_t r = (uint8_t)min(255.0f, ((COL_PATH >> 16) & 0xFF) * scale);
                    uint8_t g = (uint8_t)min(255.0f, ((COL_PATH >> 8) & 0xFF) * scale);
                    uint8_t b = (uint8_t)min(255.0f, ((COL_PATH >> 0) & 0xFF) * scale);

                    col = (0xFF << 24) | (r << 16) | (g << 8) | b;
                }
                else if (c.isCurrentPath)
                {
                    col = COL_CUR_PATH;
                }
                else if (c.visited)
                {
                    if (g_showHeatmap)
                    {
                        float t = (g_maxDist > 0) ? (float)c.distFromStart / g_maxDist : 0.0f;

                        uint8_t r = 0, g = 0, b = 0;

                        if (t < 0.5f)
                        {
                            float local_t = t * 2.0f;
                            r = 0; g = (uint8_t)(local_t * 255); b = (uint8_t)((1.0f - local_t) * 255);
                        }
                        else
                        {
                            float local_t = (t - 0.5f) * 2.0f;
                            r = (uint8_t)(local_t * 255); g = (uint8_t)((1.0f - local_t) * 255); b = 0;
                        }

                        col = (0xFF << 24) | (r << 16) | (g << 8) | b;
                    }
                    else
                    {
                        col = COL_VIS_START;
                    }
                }
                else if (c.open)
                {
                    float pulse = (sin(GetTickCount64() / 250.0 + x * y * 0.01) + 1.0f) * 0.5f * 64.0f;

                    uint8_t r = (uint8_t)min(255, int(((COL_OPEN_BASE >> 16) & 0xFF) + pulse));
                    uint8_t g = (uint8_t)min(255, int(((COL_OPEN_BASE >> 8) & 0xFF) + pulse));
                    uint8_t b = (uint8_t)min(255, int(((COL_OPEN_BASE >> 0) & 0xFF) + pulse));

                    col = (0xFF << 24) | (r << 16) | (g << 8) | b;
                }

                if (g_haveStart && x == g_start.x && y == g_start.y)
                {
                    col = COL_START;
                }
                if (g_haveEnd && x == g_end.x && y == g_end.y)
                {
                    col = COL_END;
                }

                row[x] = col;
            }
        }

        g_ctx->Unmap(g_gridTex.Get(), 0);
    }
}


HRESULT CreateDeviceAndSwapChain(HWND hwnd)
{
    DXGI_SWAP_CHAIN_DESC sd{};

    sd.BufferDesc.Width = g_winW;
    sd.BufferDesc.Height = g_winH;
    sd.BufferDesc.Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    sd.SampleDesc.Count = 1;
    sd.BufferUsage = DXGI_USAGE_RENDER_TARGET_OUTPUT;
    sd.BufferCount = 2;
    sd.OutputWindow = hwnd;
    sd.Windowed = TRUE;
    sd.SwapEffect = DXGI_SWAP_EFFECT_DISCARD;

    UINT flags = 0;

    #ifdef _DEBUG
    flags |= D3D11_CREATE_DEVICE_DEBUG;
    #endif

    D3D_FEATURE_LEVEL flvls[] = { D3D_FEATURE_LEVEL_11_1, D3D_FEATURE_LEVEL_11_0, D3D_FEATURE_LEVEL_10_0 };
    D3D_FEATURE_LEVEL flout{};

    return D3D11CreateDeviceAndSwapChain(
        nullptr, D3D_DRIVER_TYPE_HARDWARE, nullptr, flags,
        flvls, _countof(flvls), D3D11_SDK_VERSION,
        &sd, g_swap.GetAddressOf(),
        g_device.GetAddressOf(), &flout,
        g_ctx.GetAddressOf()
    );
}

HRESULT CreateBackbufferRTV()
{
    ComPtr<ID3D11Texture2D> back;

    HRESULT hr = g_swap->GetBuffer(0, __uuidof(ID3D11Texture2D), reinterpret_cast<void**>(back.GetAddressOf()));

    if (FAILED(hr))
    {
        return hr;
    }

    return g_device->CreateRenderTargetView(back.Get(), nullptr, g_rtv.GetAddressOf());
}

HRESULT CreateShadersAndQuad()
{
    ComPtr<ID3DBlob> vsb, psb, err;

    HRESULT hr = D3DCompile(VS_SRC, (UINT)strlen(VS_SRC), nullptr, nullptr, nullptr, "main", "vs_5_0", 0, 0, vsb.GetAddressOf(), err.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    err.Reset();

    hr = D3DCompile(PS_SRC, (UINT)strlen(PS_SRC), nullptr, nullptr, nullptr, "main", "ps_5_0", 0, 0, psb.GetAddressOf(), err.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    hr = g_device->CreateVertexShader(vsb->GetBufferPointer(), vsb->GetBufferSize(), nullptr, g_vs.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    hr = g_device->CreatePixelShader(psb->GetBufferPointer(), psb->GetBufferSize(), nullptr, g_ps.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    D3D11_INPUT_ELEMENT_DESC il[] =
    {
        {"POSITION",0,DXGI_FORMAT_R32G32B32_FLOAT,0,0 ,D3D11_INPUT_PER_VERTEX_DATA,0},
        {"TEXCOORD",0,DXGI_FORMAT_R32G32_FLOAT,   0,12 ,D3D11_INPUT_PER_VERTEX_DATA,0},
    };

    hr = g_device->CreateInputLayout(il, 2, vsb->GetBufferPointer(), vsb->GetBufferSize(), g_il.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    D3D11_BUFFER_DESC bd{};

    bd.BindFlags = D3D11_BIND_VERTEX_BUFFER;
    bd.ByteWidth = sizeof(QUAD);
    bd.Usage = D3D11_USAGE_IMMUTABLE;

    D3D11_SUBRESOURCE_DATA init{ QUAD, 0, 0 };

    return g_device->CreateBuffer(&bd, &init, g_vb.GetAddressOf());
}

HRESULT CreateGridTexture()
{
    D3D11_TEXTURE2D_DESC td{};

    td.Width = GRID_W;
    td.Height = GRID_H;
    td.MipLevels = 1;
    td.ArraySize = 1;
    td.Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    td.SampleDesc.Count = 1;
    td.Usage = D3D11_USAGE_DYNAMIC;
    td.BindFlags = D3D11_BIND_SHADER_RESOURCE;
    td.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;

    HRESULT hr = g_device->CreateTexture2D(&td, nullptr, g_gridTex.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    D3D11_SHADER_RESOURCE_VIEW_DESC sd{};

    sd.Format = td.Format;
    sd.ViewDimension = D3D11_SRV_DIMENSION_TEXTURE2D;
    sd.Texture2D.MipLevels = 1;
    hr = g_device->CreateShaderResourceView(g_gridTex.Get(), &sd, g_gridSRV.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    UpdateGridTexture();

    return S_OK;
}

void Resize(UINT w, UINT h)
{
    if (!g_device)
    {
        return;
    }

    g_ctx->OMSetRenderTargets(0, nullptr, nullptr);
    g_rtv.Reset();
    g_vp = { 0,0,(float)w,(float)h,0.0f,1.0f };
    g_swap->ResizeBuffers(0, w, h, DXGI_FORMAT_UNKNOWN, 0);

    CreateBackbufferRTV();

    g_winW = w; g_winH = h;
}

HRESULT CreateLineShaders()
{
    ComPtr<ID3DBlob> vsb, psb, err;

    HRESULT hr = D3DCompile(VS_LINES, (UINT)strlen(VS_LINES), nullptr, nullptr, nullptr, "main", "vs_5_0", 0, 0, vsb.GetAddressOf(), err.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    err.Reset();

    hr = D3DCompile(PS_LINES, (UINT)strlen(PS_LINES), nullptr, nullptr, nullptr, "main", "ps_5_0", 0, 0, psb.GetAddressOf(), err.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    hr = g_device->CreateVertexShader(vsb->GetBufferPointer(), vsb->GetBufferSize(), nullptr, g_vsLines.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    hr = g_device->CreatePixelShader(psb->GetBufferPointer(), psb->GetBufferSize(), nullptr, g_psLines.GetAddressOf());

    if (FAILED(hr))
    {
        return hr;
    }

    D3D11_INPUT_ELEMENT_DESC il[] =
    {
        {"POSITION",0,DXGI_FORMAT_R32G32_FLOAT,0,0,D3D11_INPUT_PER_VERTEX_DATA,0},
    };

    return g_device->CreateInputLayout(il, 1, vsb->GetBufferPointer(), vsb->GetBufferSize(), g_ilLines.GetAddressOf());
}

void BuildGridLines()
{
    const UINT vLines = GRID_W + 1;
    const UINT hLines = GRID_H + 1;

    g_gridLineVertCount = 2 * (vLines + hLines);

    vector<LineVtx> verts;
    verts.reserve(g_gridLineVertCount);

    auto toClipX = [](float u) { return u * 2.0f - 1.0f; };
    auto toClipY = [](float v) { return 1.0f - v * 2.0f; };

    for (UINT i = 0; i <= GRID_W; ++i)
    {
        float u = i / float(GRID_W);
        float x = toClipX(u);

        verts.push_back({ x, toClipY(0.0f) });
        verts.push_back({ x, toClipY(1.0f) });
    }
    for (UINT j = 0; j <= GRID_H; ++j)
    {
        float v = j / float(GRID_H);
        float y = toClipY(v);

        verts.push_back({ toClipX(0.0f), y });
        verts.push_back({ toClipX(1.0f), y });
    }

    D3D11_BUFFER_DESC bd{};

    bd.BindFlags = D3D11_BIND_VERTEX_BUFFER;
    bd.ByteWidth = UINT(verts.size() * sizeof(LineVtx));
    bd.Usage = D3D11_USAGE_IMMUTABLE;

    D3D11_SUBRESOURCE_DATA init{};

    init.pSysMem = verts.data();

    g_gridLineVB.Reset();
    g_device->CreateBuffer(&bd, &init, g_gridLineVB.GetAddressOf());
}

void RenderGridLines()
{
    if (!g_gridLineVB)
    {
        return;
    }

    UINT stride = sizeof(LineVtx), offset = 0;

    g_ctx->IASetVertexBuffers(0, 1, g_gridLineVB.GetAddressOf(), &stride, &offset);
    g_ctx->IASetPrimitiveTopology(D3D11_PRIMITIVE_TOPOLOGY_LINELIST);
    g_ctx->IASetInputLayout(g_ilLines.Get());
    g_ctx->VSSetShader(g_vsLines.Get(), nullptr, 0);
    g_ctx->PSSetShader(g_psLines.Get(), nullptr, 0);
    g_ctx->Draw(g_gridLineVertCount, 0);
}

void Render()
{
    DWORD currentTime = GetTickCount64();

    if (g_searchRunning && (currentTime - g_lastUpdateTime > UPDATE_INTERVAL_MS))
    {
        StepSearchAnimated(EXPANSIONS_PER_FRAME);

        g_lastUpdateTime = currentTime;
    }
    else if (g_pathAnimIndex != -1 && (currentTime - g_lastUpdateTime > PATH_ANIM_INTERVAL_MS))
    {
        int nodeIdx = g_finalPathNodes[g_pathAnimIndex];
        int x = nodeIdx % GRID_W, y = nodeIdx / GRID_W;

        g_grid[y][x].path = true;
        g_pathAnimIndex--;
        g_lastUpdateTime = currentTime;
    }

    TraceCurrentPath();

    UpdateGridTexture();

    const float clear[4] = { 0.08f,0.08f,0.09f,1.0f };

    g_ctx->OMSetRenderTargets(1, g_rtv.GetAddressOf(), nullptr);
    g_ctx->ClearRenderTargetView(g_rtv.Get(), clear);
    g_vp = { 0,0,(float)g_winW,(float)g_winH,0,1 };
    g_ctx->RSSetViewports(1, &g_vp);

    UINT stride = sizeof(Vtx), offset = 0;

    g_ctx->IASetVertexBuffers(0, 1, g_vb.GetAddressOf(), &stride, &offset);
    g_ctx->IASetPrimitiveTopology(D3D11_PRIMITIVE_TOPOLOGY_TRIANGLELIST);
    g_ctx->IASetInputLayout(g_il.Get());
    g_ctx->VSSetShader(g_vs.Get(), nullptr, 0);
    g_ctx->PSSetShader(g_ps.Get(), nullptr, 0);

    ID3D11ShaderResourceView* srvs[1] = { g_gridSRV.Get() };

    g_ctx->PSSetShaderResources(0, 1, srvs);

    ComPtr<ID3D11SamplerState> samp;

    D3D11_SAMPLER_DESC sd{};

    sd.Filter = D3D11_FILTER_MIN_MAG_MIP_POINT;
    sd.AddressU = sd.AddressV = sd.AddressW = D3D11_TEXTURE_ADDRESS_CLAMP;

    g_device->CreateSamplerState(&sd, samp.GetAddressOf());
    g_ctx->PSSetSamplers(0, 1, samp.GetAddressOf());
    g_ctx->Draw(6, 0);

    RenderGridLines();

    g_swap->Present(1, 0);
}

POINT ToGrid(int mouseX, int mouseY)
{
    int gx = (int)((mouseX / (float)g_winW) * GRID_W);
    int gy = (int)((mouseY / (float)g_winH) * GRID_H);

    if (gx < 0)
    {
        gx = 0;
    }
    if (gy < 0)
    {
        gy = 0;
    }
    if (gx >= GRID_W)
    {
        gx = GRID_W - 1;
    }
    if (gy >= GRID_H)
    {
        gy = GRID_H - 1;
    }

    return { gx, gy };
}

void StartOrRestartSearchIfNeeded()
{
    if (g_haveStart && g_haveEnd)
    {
        InitSearchAnimated();
    }
    else
    {
        g_searchRunning = false;
    }
}

void HandleLeftClick(POINT p)
{
    if (!g_grid[p.y][p.x].wall)
    {
        if (!g_haveStart)
        {
            g_start = p; g_haveStart = true;
        }
        else if (!g_haveEnd)
        {
            g_end = p; g_haveEnd = true;
        }
        else
        {
            g_end = p;
        }
    }

    StartOrRestartSearchIfNeeded();
}

void HandleRightPaint(POINT p, bool shiftDown)
{
    if ((g_haveStart && p.x == g_start.x && p.y == g_start.y) || (g_haveEnd && p.x == g_end.x && p.y == g_end.y))
    {
        return;
    }

    Cell& c = g_grid[p.y][p.x];

    bool newState = !shiftDown;

    if (c.wall != newState)
    {
        if (!g_wallHistory.empty())
        {
            g_wallHistory.back().push_back({ p.x, p.y, c.wall });
        }

        c.wall = newState;
    }

    StartOrRestartSearchIfNeeded();
}

void UndoWall()
{
    if (g_wallHistory.empty())
    {
        return;
    }

    const vector<WallChange>& lastStroke = g_wallHistory.back();

    for (const auto& change : lastStroke)
    {
        g_grid[change.y][change.x].wall = change.prevState;
    }

    g_wallHistory.pop_back();

    StartOrRestartSearchIfNeeded();
}

void UpdateWindowTitle()
{
    if (!g_hwnd)
    {
        return;
    }

    wstring algoName = (g_currentAlgorithm == SearchAlgorithm::AStar) ? L"A* Search" : L"Dijkstra";
    wstring moveMode = g_allowDiagonals ? L" (Diagonals)" : L"";
    wstring costMode = L"";

    if (g_allowDiagonals)
    {
        costMode = g_useWeightedCosts ? L" [Weighted]" : L" [Unweighted]";
    }

    wstring title = algoName + moveMode + costMode + L" | Visited: " + to_wstring(g_stats.nodesVisited);

    if (g_stats.pathLength > 0)
    {
        title += L" | Path Steps: " + to_wstring(g_stats.pathLength);
    }
    else if (!g_searchRunning && g_haveStart && g_haveEnd && g_pq.empty())
    {
        title += L" | Path: Not Found";
    }

    SetWindowTextW(g_hwnd, title.c_str());
}

LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    switch (msg)
    {
    case WM_DESTROY:

        PostQuitMessage(0);

        return 0;

    case WM_SIZE:

        if (g_swap)
        {
            UINT w = LOWORD(lParam), h = HIWORD(lParam);

            if (w > 0 && h > 0)
            {
                Resize(w, h);
            }
        }
        return 0;

    case WM_KEYDOWN:

        if (wParam == VK_ESCAPE)
        {
            DestroyWindow(hwnd);
        }
        else if (wParam == 'R')
        {
            ClearGrid(false); g_searchRunning = false; g_wallHistory.clear();
        }
        else if (wParam == 'C')
        {
            ClearGrid(true); g_searchRunning = false;
        }
        else if (wParam == 'M')
        {
            GenerateMaze_RecursiveBacktracker();
        }
        else if (wParam == 'H')
        {
            g_showHeatmap = !g_showHeatmap;
        }
        else if (wParam == 'A')
        {
            g_currentAlgorithm = (g_currentAlgorithm == SearchAlgorithm::Dijkstra) ? SearchAlgorithm::AStar : SearchAlgorithm::Dijkstra;

            StartOrRestartSearch();

            UpdateWindowTitle();
        }
        else if (wParam == 'D')
        {
            g_allowDiagonals = !g_allowDiagonals;

            StartOrRestartSearch();

            UpdateWindowTitle();
        }
        else if (wParam == 'W')
        {
            g_useWeightedCosts = !g_useWeightedCosts;

            StartOrRestartSearch();

            UpdateWindowTitle();
        }
        else if (wParam == 'Z' && (GetKeyState(VK_CONTROL) & 0x8000))
        {
            UndoWall();
        }

        return 0;

    case WM_LBUTTONDOWN:
    {
        HandleLeftClick(ToGrid(GET_X_LPARAM(lParam), GET_Y_LPARAM(lParam)));

        return 0;
    }

    case WM_RBUTTONDOWN:
    {
        g_mouseRDown = true;
        g_wallHistory.push_back({});

        bool shift = (GetKeyState(VK_SHIFT) & 0x8000) != 0;

        HandleRightPaint(ToGrid(GET_X_LPARAM(lParam), GET_Y_LPARAM(lParam)), shift);

        return 0;
    }
    case WM_MOUSEMOVE:

        if (g_mouseRDown)
        {
            bool shift = (GetKeyState(VK_SHIFT) & 0x8000) != 0;

            HandleRightPaint(ToGrid(GET_X_LPARAM(lParam), GET_Y_LPARAM(lParam)), shift);
        }

        return 0;

    case WM_RBUTTONUP:

        g_mouseRDown = false;

        if (!g_wallHistory.empty() && g_wallHistory.back().empty())
        {
            g_wallHistory.pop_back();
        }

        return 0;
    }

    return DefWindowProc(hwnd, msg, wParam, lParam);
}

int WINAPI WinMain(HINSTANCE hInst, HINSTANCE, LPSTR, int)
{
    WNDCLASS wc{};

    wc.style = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInst;
    wc.lpszClassName = L"DXPathfindingWnd";
    wc.hCursor = LoadCursor(nullptr, IDC_ARROW);

    RegisterClass(&wc);

    RECT r{ 0,0,(LONG)g_winW,(LONG)g_winH };

    AdjustWindowRect(&r, WS_OVERLAPPEDWINDOW, FALSE);

    g_hwnd = CreateWindow(wc.lpszClassName, L"", WS_OVERLAPPEDWINDOW | WS_VISIBLE, CW_USEDEFAULT, CW_USEDEFAULT,
        r.right - r.left, r.bottom - r.top, nullptr, nullptr, hInst, nullptr);

    UpdateWindowTitle();

    if (FAILED(CreateDeviceAndSwapChain(g_hwnd)))
    {
        return 0;
    }
    if (FAILED(CreateBackbufferRTV()))
    {
        return 0;
    }
    if (FAILED(CreateShadersAndQuad()))
    {
        return 0;
    }
    if (FAILED(CreateLineShaders()))
    {
        return 0;
    }

    BuildGridLines();

    if (FAILED(CreateGridTexture()))
    {
        return 0;
    }

    MSG msg{};

    while (true)
    {
        while (PeekMessage(&msg, nullptr, 0, 0, PM_REMOVE))
        {
            if (msg.message == WM_QUIT)
            {
                goto exit;
            }

            TranslateMessage(&msg);

            DispatchMessage(&msg);
        }

        Render();
    }

exit:

    return (int)msg.wParam;
}