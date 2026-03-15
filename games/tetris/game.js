// ========== グローバル変数 ==========
// canvas等はDOMContentLoaded後に取得する（先頭でnullになるのを防ぐ）
let canvas, ctx, holdCanvas, holdCtx, nextCanvas, nextCtx;

function initCanvases() {
  canvas = document.getElementById("game");
  ctx = canvas?.getContext("2d");
  holdCanvas = document.getElementById("holdCanvas");
  holdCtx = holdCanvas?.getContext("2d");
  nextCanvas = document.getElementById("nextCanvas");
  nextCtx = nextCanvas?.getContext("2d");
}

const COLS = 10;
const ROWS = 20;
const BLOCK_SIZE = 24;

const COLORS = {
  I: "#0ff", J: "#00f", L: "#f80",
  O: "#ff0", S: "#0f0", T: "#a0f", Z: "#f00"
};

const SHAPES = {
  I: [[0,0,0,0],[1,1,1,1],[0,0,0,0],[0,0,0,0]],
  J: [[1,0,0],[1,1,1],[0,0,0]],
  L: [[0,0,1],[1,1,1],[0,0,0]],
  O: [[1,1],[1,1]],
  S: [[0,1,1],[1,1,0],[0,0,0]],
  T: [[0,1,0],[1,1,1],[0,0,0]],
  Z: [[1,1,0],[0,1,1],[0,0,0]]
};

const WALL_KICKS = {
  JLSTZ: {
    '0->R': [[0,0],[-1,0],[-1,1],[0,-2],[-1,-2]],
    'R->0': [[0,0],[1,0],[1,-1],[0,2],[1,2]],
    'R->2': [[0,0],[1,0],[1,-1],[0,2],[1,2]],
    '2->R': [[0,0],[-1,0],[-1,1],[0,-2],[-1,-2]],
    '2->L': [[0,0],[1,0],[1,1],[0,-2],[1,-2]],
    'L->2': [[0,0],[-1,0],[-1,-1],[0,2],[-1,2]],
    'L->0': [[0,0],[-1,0],[-1,-1],[0,2],[-1,2]],
    '0->L': [[0,0],[1,0],[1,1],[0,-2],[1,-2]]
  },
  I: {
    '0->R': [[0,0],[-2,0],[1,0],[-2,-1],[1,2]],
    'R->0': [[0,0],[2,0],[-1,0],[2,1],[-1,-2]],
    'R->2': [[0,0],[-1,0],[2,0],[-1,2],[2,-1]],
    '2->R': [[0,0],[1,0],[-2,0],[1,-2],[-2,1]],
    '2->L': [[0,0],[2,0],[-1,0],[2,1],[-1,-2]],
    'L->2': [[0,0],[-2,0],[1,0],[-2,-1],[1,2]],
    'L->0': [[0,0],[1,0],[-2,0],[1,-2],[-2,1]],
    '0->L': [[0,0],[-1,0],[2,0],[-1,2],[2,-1]]
  }
};

// ゲーム状態
let field, current, nextPiece, heldPiece, canHold;
let score, highscore, username;
let gameOver, dropCounter, lastTime, lockDelay, moveResets, rotationState;
let combo, backToBack, totalLinesCleared;
let bag = [];
let gameEndHandled = false;

// CPU 1v1 対戦用
let cpuOpponent = null;
let cpuIntervalId = null;
let isPaused = false;
let cpuLevel = null; // 1-5: 練習モード、null: ランクマッチ
let pendingMode = null; // 'single' or 'cpu1v1'

// レーティングシステム
let rating = 1000;
let winStreak = 0;
let currentRank = 'C';

// オンライン
let ws, isOnline, roomId, clientId, gameMode, isHost;
let onlinePlayers = new Map();
let miniCanvases = new Map();
let isSpectating = false;
let spectateIndex = 0;
let spectatingPlayers = [];
let matchTimer = null;
let matchTimeLeft = 60;
let allPlayersData = new Map();
let connectionRetries = 0;
let maxRetries = 3;
let retryTimeout = null;
let lastFieldUpdate = 0; // フィールド更新タイマー
let fieldUpdateInterval = 500; // 500msごとに更新

// 設定
let serverUrl = "wss://tetris.mamechosu.f5.si/";
const lockDelayLimit = 500;
const maxMoveResets = 15;

// キー設定
let keys = {
  left: 'ArrowLeft',
  right: 'ArrowRight',
  rotateL: 'z',
  rotateR: 'x',
  softDrop: 'ArrowDown',
  hardDrop: ' ',
  hold: 'c'
};

// ========== レーティングシステム ==========
function getRank(ratingValue) {
  if (ratingValue >= 2000) return 'S++';
  if (ratingValue >= 1800) return 'S+';
  if (ratingValue >= 1600) return 'S';
  if (ratingValue >= 1400) return 'A';
  if (ratingValue >= 1200) return 'B';
  if (ratingValue >= 1000) return 'C';
  if (ratingValue >= 800) return 'D';
  if (ratingValue >= 600) return 'E';
  return 'F';
}

function calculateRatingChange(position, totalPlayers, mode) {
  if (mode === 'single') {
    // シングル：スコアに応じてレートが上がる（小さいボーナス）
    if (score >= 10000) return 15;
    if (score >= 5000) return 10;
    if (score >= 2000) return 5;
    if (score >= 500) return 2;
    return 0;
  }
  if (mode === 'cpu1v1') {
    // CPU 1v1：勝ち/負けでレート変動
    return position === 1 ? 20 : -10;
  }
  // オンライン・プライベート
  if (position === 1) return 30;
  if (position === 2) return 10;
  if (position === 3) return 0;
  return -15;
}

function updateRating(position, totalPlayers) {
  // 練習モード（レベル選択）はレート変動なし
  if (cpuLevel !== null) {
    return { change: 0, oldRank: currentRank, newRank: currentRank, oldRating: rating };
  }
  
  const change = calculateRatingChange(position, totalPlayers, gameMode);
  const oldRating = rating;
  const oldRank = getRank(oldRating);
  
  rating += change;
  rating = Math.max(0, rating);
  currentRank = getRank(rating);
  
  if (position === 1) {
    winStreak++;
  } else {
    winStreak = 0;
  }
  
  saveSettings();
  return { change, oldRank, newRank: currentRank, oldRating };
}

// ========== データ暗号化 ==========
async function hashData(data) {
  try {
    // crypto.subtleが使える場合
    if (window.crypto && window.crypto.subtle) {
      const encoder = new TextEncoder();
      const dataString = JSON.stringify(data);
      const dataBuffer = encoder.encode(dataString);
      const hashBuffer = await crypto.subtle.digest('SHA-256', dataBuffer);
      const hashArray = Array.from(new Uint8Array(hashBuffer));
      return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
    } else {
      // フォールバック: 簡易ハッシュ
      const dataString = JSON.stringify(data);
      let hash = 0;
      for (let i = 0; i < dataString.length; i++) {
        const char = dataString.charCodeAt(i);
        hash = ((hash << 5) - hash) + char;
        hash = hash & hash;
      }
      return Math.abs(hash).toString(16).padStart(16, '0');
    }
  } catch(e) {
    console.error('Hash error:', e);
    return '0000000000000000';
  }
}

async function encryptData(data) {
  try {
    const hash = await hashData(data);
    return {
      data: data,
      hash: hash,
      version: 1
    };
  } catch(e) {
    console.error('Encrypt error:', e);
    return { data: data, hash: '0', version: 1 };
  }
}

async function verifyData(encryptedData) {
  try {
    if (!encryptedData.hash || !encryptedData.data) return null;
    
    const calculatedHash = await hashData(encryptedData.data);
    if (calculatedHash !== encryptedData.hash) {
      console.warn('Data hash mismatch, but accepting anyway');
      return encryptedData.data;
    }
    
    return encryptedData.data;
  } catch(e) {
    console.error('Verify error:', e);
    return encryptedData.data || null;
  }
}

// ========== 初期化 ==========
function generateRandomId() {
  return Math.floor(Math.random() * 100000000).toString().padStart(8, '0');
}

async function initializeGame() {
  // 変数を先に初期化
  username = "Player" + generateRandomId();
  highscore = 0;
  score = 0;
  rating = 1000;
  winStreak = 0;
  currentRank = 'C';
  
  // データ読み込み
  await loadSettings();
  
  // UI更新
  updateTitleStats();
  updateUI();
}

function updateTitleStats() {
  // プレイヤー情報モーダルの表示
  const displayRank = document.getElementById('displayRank');
  const displayRating = document.getElementById('displayRating');
  const displayWinStreak = document.getElementById('displayWinStreak');
  const displayHighScore = document.getElementById('displayHighScore');
  const displayUsername = document.getElementById('displayUsername');
  
  if (displayRank) displayRank.textContent = currentRank || 'F';
  if (displayRating) displayRating.textContent = rating || 1000;
  if (displayWinStreak) displayWinStreak.textContent = winStreak || 0;
  if (displayHighScore) displayHighScore.textContent = (highscore || 0).toLocaleString();
  if (displayUsername) displayUsername.textContent = username || 'Player';
  
  // レート進捗バーの更新
  updateRatingProgressBar();
}

function updateRatingProgressBar() {
  const ratingValue = rating || 1000;
  
  // 現在のランクの範囲を取得
  const rankRanges = {
    'S++': [2000, 9999],
    'S+': [1800, 1999],
    'S': [1600, 1799],
    'A': [1400, 1599],
    'B': [1200, 1399],
    'C': [1000, 1199],
    'D': [800, 999],
    'E': [600, 799],
    'F': [0, 599]
  };
  
  const [minRating, maxRating] = rankRanges[currentRank] || [1000, 1199];
  const nextRankMin = maxRating + 1;
  const rangeSize = maxRating - minRating + 1;
  const progress = ((ratingValue - minRating) / rangeSize) * 100;
  const toNext = maxRating - ratingValue + 1;
  
  const progressBar = document.getElementById('ratingProgressBar');
  const progressText = document.getElementById('ratingProgressText');
  const currentRankMin = document.getElementById('currentRankMin');
  const nextRankMinElem = document.getElementById('nextRankMin');
  
  if (progressBar) {
    progressBar.style.width = Math.max(0, Math.min(100, progress)) + '%';
  }
  
  if (progressText) {
    if (currentRank === 'S++') {
      progressText.textContent = '最高ランク！';
    } else {
      progressText.textContent = `次のランクまで ${toNext}`;
    }
  }
  
  if (currentRankMin) currentRankMin.textContent = minRating;
  if (nextRankMinElem) {
    if (currentRank === 'S++') {
      nextRankMinElem.textContent = '∞';
    } else {
      nextRankMinElem.textContent = nextRankMin;
    }
  }
}

// ========== 画面遷移 ==========
function showScreen(screenId) {
  document.querySelectorAll('.screen').forEach(s => s.classList.remove('active'));
  const screen = document.getElementById(screenId);
  if (screen) screen.classList.add('active');
}

function hideAllPanels() {
  document.querySelectorAll('.sub-panel').forEach(p => p.classList.remove('active'));
}

function showLevelSelect() {
  const menuOptions = document.querySelector('.menu-options');
  const levelSelect = document.getElementById('cpuLevelSelect');
  const btnBack = document.getElementById('btnBackToStart');
  
  if (menuOptions) menuOptions.style.display = 'none';
  if (levelSelect) levelSelect.style.display = 'block';
  if (btnBack) btnBack.style.display = 'none';
}

function hideLevelSelect() {
  const menuOptions = document.querySelector('.menu-options');
  const levelSelect = document.getElementById('cpuLevelSelect');
  const btnBack = document.getElementById('btnBackToStart');
  
  if (menuOptions) menuOptions.style.display = '';
  if (levelSelect) levelSelect.style.display = 'none';
  if (btnBack) btnBack.style.display = '';
  pendingMode = null;
}

window.hideAllPanels = hideAllPanels;

// ========== イベントリスナー ==========
document.addEventListener('DOMContentLoaded', async () => {
  console.log('DOM loaded, initializing...');
  try {
    initCanvases();
    await initializeGame();
  } catch(e) {
    console.error('Init error:', e);
  }
  
  // タイトル画面
  const btnStart = document.getElementById('btnStart');
  if (btnStart) {
    const startHandler = () => {
      console.log('Start button clicked');
      showScreen('menuScreen');
    };
    btnStart.addEventListener('click', startHandler);
    btnStart.addEventListener('touchend', (e) => {
      e.preventDefault();
      startHandler();
    });
  }
  
  const btnViewStats = document.getElementById('btnViewStats');
  if (btnViewStats) {
    const viewStatsHandler = () => {
      console.log('View stats clicked');
      const statsModal = document.getElementById('statsModal');
      if (statsModal) {
        statsModal.classList.add('active');
        updateRatingProgressBar();
      }
    };
    btnViewStats.addEventListener('click', viewStatsHandler);
    btnViewStats.addEventListener('touchend', (e) => {
      e.preventDefault();
      viewStatsHandler();
    });
  }
  
  const btnCloseStats = document.getElementById('btnCloseStats');
  if (btnCloseStats) {
    const closeStatsHandler = () => {
      const statsModal = document.getElementById('statsModal');
      if (statsModal) {
        statsModal.classList.remove('active');
      }
    };
    btnCloseStats.addEventListener('click', closeStatsHandler);
    btnCloseStats.addEventListener('touchend', (e) => {
      e.preventDefault();
      closeStatsHandler();
    });
  }
  
  // メニュー画面
  const btnSingle = document.getElementById('btnSingle');
  if (btnSingle) {
    btnSingle.addEventListener('click', () => { pendingMode = 'single'; showLevelSelect(); });
    btnSingle.addEventListener('touchend', (e) => { e.preventDefault(); pendingMode = 'single'; showLevelSelect(); });
  }
  
  const btnCPU1v1 = document.getElementById('btnCPU1v1');
  if (btnCPU1v1) {
    btnCPU1v1.addEventListener('click', () => { pendingMode = 'cpu1v1'; showLevelSelect(); });
    btnCPU1v1.addEventListener('touchend', (e) => { e.preventDefault(); pendingMode = 'cpu1v1'; showLevelSelect(); });
  }
  
  const btnCreateRoom = document.getElementById('btnCreateRoom');
  if (btnCreateRoom) {
    const createRoomHandler = () => {
      hideAllPanels();
      const panel = document.getElementById('createRoomPanel');
      if (panel) panel.classList.add('active');
    };
    btnCreateRoom.addEventListener('click', createRoomHandler);
    btnCreateRoom.addEventListener('touchend', (e) => { e.preventDefault(); createRoomHandler(); });
  }
  
  const btnJoinRoom = document.getElementById('btnJoinRoom');
  if (btnJoinRoom) {
    const joinRoomHandler = () => {
      hideAllPanels();
      const panel = document.getElementById('joinRoomPanel');
      if (panel) panel.classList.add('active');
    };
    btnJoinRoom.addEventListener('click', joinRoomHandler);
    btnJoinRoom.addEventListener('touchend', (e) => { e.preventDefault(); joinRoomHandler(); });
  }
  
  const btnOptions = document.getElementById('btnOptions');
  if (btnOptions) {
    const optionsHandler = () => {
      const panel = document.getElementById('optionsPanel');
      if (panel) {
        if (panel.classList.contains('active')) {
          panel.classList.remove('active');
        } else {
          hideAllPanels();
          panel.classList.add('active');
        }
      }
    };
    btnOptions.addEventListener('click', optionsHandler);
    btnOptions.addEventListener('touchend', (e) => {
      e.preventDefault();
      optionsHandler();
    });
  }
  
  const btnBackToStart = document.getElementById('btnBackToStart');
  if (btnBackToStart) {
    const backHandler = () => {
      showScreen('startScreen');
      hideAllPanels();
      if (ws) ws.close();
    };
    btnBackToStart.addEventListener('click', backHandler);
    btnBackToStart.addEventListener('touchend', (e) => {
      e.preventDefault();
      backHandler();
    });
  }
  
  // ルーム操作
  const btnDoCreateRoom = document.getElementById('btnDoCreateRoom');
  if (btnDoCreateRoom) {
    const createHandler = () => createRoom();
    btnDoCreateRoom.addEventListener('click', createHandler);
    btnDoCreateRoom.addEventListener('touchend', (e) => {
      e.preventDefault();
      createHandler();
    });
  }
  
  const btnCancelCreate = document.getElementById('btnCancelCreate');
  if (btnCancelCreate) {
    const cancelCreateHandler = () => hideAllPanels();
    btnCancelCreate.addEventListener('click', cancelCreateHandler);
    btnCancelCreate.addEventListener('touchend', (e) => {
      e.preventDefault();
      cancelCreateHandler();
    });
  }
  
  const btnDoJoinRoom = document.getElementById('btnDoJoinRoom');
  if (btnDoJoinRoom) {
    const joinHandler = () => {
      const roomCode = document.getElementById('roomCodeInput')?.value;
      if (roomCode && confirm(`ルーム "${roomCode}" に参加しますか？`)) {
        joinRoom();
      }
    };
    btnDoJoinRoom.addEventListener('click', joinHandler);
    btnDoJoinRoom.addEventListener('touchend', (e) => {
      e.preventDefault();
      joinHandler();
    });
  }
  
  const btnCancelJoin = document.getElementById('btnCancelJoin');
  if (btnCancelJoin) {
    const cancelJoinHandler = () => hideAllPanels();
    btnCancelJoin.addEventListener('click', cancelJoinHandler);
    btnCancelJoin.addEventListener('touchend', (e) => {
      e.preventDefault();
      cancelJoinHandler();
    });
  }
  
  // 待機画面
  const btnStartGame = document.getElementById('btnStartGame');
  if (btnStartGame) {
    const startGameHandler = () => hostStartGame();
    btnStartGame.addEventListener('click', startGameHandler);
    btnStartGame.addEventListener('touchend', (e) => {
      e.preventDefault();
      startGameHandler();
    });
  }
  
  const btnLeaveRoom = document.getElementById('btnLeaveRoom');
  if (btnLeaveRoom) {
    const leaveHandler = () => leaveRoom();
    btnLeaveRoom.addEventListener('click', leaveHandler);
    btnLeaveRoom.addEventListener('touchend', (e) => {
      e.preventDefault();
      leaveHandler();
    });
  }
  
  // ゲームオーバー
  const btnRestart = document.getElementById('btnRestart');
  if (btnRestart) {
    const restartHandler = () => restartGame();
    btnRestart.addEventListener('click', restartHandler);
    btnRestart.addEventListener('touchend', (e) => {
      e.preventDefault();
      restartHandler();
    });
  }
  
  const btnBackToMenu = document.getElementById('btnBackToMenu');
  if (btnBackToMenu) {
    const backToMenuHandler = () => {
      const gameOverModal = document.getElementById('gameOverModal');
      const spectateMode = document.getElementById('spectateMode');
      if (gameOverModal) gameOverModal.classList.remove('active');
      if (spectateMode) spectateMode.classList.remove('active');
      showScreen('menuScreen');
      if (ws) ws.close();
      isOnline = false;
      isSpectating = false;
    };
    btnBackToMenu.addEventListener('click', backToMenuHandler);
    btnBackToMenu.addEventListener('touchend', (e) => {
      e.preventDefault();
      backToMenuHandler();
    });
  }
  
  // 観戦モード
  const btnPrevPlayer = document.getElementById('btnPrevPlayer');
  if (btnPrevPlayer) {
    const prevHandler = () => {
      if (spectateIndex > 0) {
        spectateIndex--;
        updateSpectateView();
      }
    };
    btnPrevPlayer.addEventListener('click', prevHandler);
    btnPrevPlayer.addEventListener('touchend', (e) => {
      e.preventDefault();
      prevHandler();
    });
  }
  
  const btnNextPlayer = document.getElementById('btnNextPlayer');
  if (btnNextPlayer) {
    const nextHandler = () => {
      if (spectateIndex < spectatingPlayers.length - 1) {
        spectateIndex++;
        updateSpectateView();
      }
    };
    btnNextPlayer.addEventListener('click', nextHandler);
    btnNextPlayer.addEventListener('touchend', (e) => {
      e.preventDefault();
      nextHandler();
    });
  }
  
  const btnExitSpectate = document.getElementById('btnExitSpectate');
  if (btnExitSpectate) {
    const exitHandler = () => exitSpectate();
    btnExitSpectate.addEventListener('click', exitHandler);
    btnExitSpectate.addEventListener('touchend', (e) => {
      e.preventDefault();
      exitHandler();
    });
  }
  
  // チャット送信
  const btnSendChat = document.getElementById('btnSendChat');
  if (btnSendChat) {
    const sendHandler = () => sendChat();
    btnSendChat.addEventListener('click', sendHandler);
    btnSendChat.addEventListener('touchend', (e) => {
      e.preventDefault();
      sendHandler();
    });
  }
  
  const chatInput = document.getElementById('chatInput');
  if (chatInput) {
    chatInput.addEventListener('keypress', (e) => {
      if (e.key === 'Enter') {
        e.preventDefault();
        sendChat();
      }
    });
  }
  
  // データ保存/読込
  const btnSaveData = document.getElementById('btnSaveData');
  if (btnSaveData) {
    const saveHandler = () => saveData();
    btnSaveData.addEventListener('click', saveHandler);
    btnSaveData.addEventListener('touchend', (e) => {
      e.preventDefault();
      saveHandler();
    });
  }
  
  const btnLoadData = document.getElementById('btnLoadData');
  if (btnLoadData) {
    const loadHandler = () => {
      const fileInput = document.getElementById('fileInput');
      if (fileInput) fileInput.click();
    };
    btnLoadData.addEventListener('click', loadHandler);
    btnLoadData.addEventListener('touchend', (e) => {
      e.preventDefault();
      loadHandler();
    });
  }
  
  const btnResetKeys = document.getElementById('btnResetKeys');
  if (btnResetKeys) {
    const resetHandler = () => resetKeys();
    btnResetKeys.addEventListener('click', resetHandler);
    btnResetKeys.addEventListener('touchend', (e) => {
      e.preventDefault();
      resetHandler();
    });
  }
  
  // 接続エラー
  const btnRetry = document.getElementById('btnRetry');
  if (btnRetry) {
    const retryHandler = () => retryConnection();
    btnRetry.addEventListener('click', retryHandler);
    btnRetry.addEventListener('touchend', (e) => { e.preventDefault(); retryHandler(); });
  }
  
  // レベル選択
  for (let lv = 1; lv <= 5; lv++) {
    const btn = document.getElementById(`btnLevel${lv}`);
    if (btn) {
      btn.addEventListener('click', () => startWithLevel(lv));
      btn.addEventListener('touchend', (e) => { e.preventDefault(); startWithLevel(lv); });
    }
  }
  
  const btnRankedMode = document.getElementById('btnRankedMode');
  if (btnRankedMode) {
    btnRankedMode.addEventListener('click', () => startWithLevel(null));
    btnRankedMode.addEventListener('touchend', (e) => { e.preventDefault(); startWithLevel(null); });
  }
  
  const btnCancelLevel = document.getElementById('btnCancelLevel');
  if (btnCancelLevel) {
    btnCancelLevel.addEventListener('click', hideLevelSelect);
    btnCancelLevel.addEventListener('touchend', (e) => { e.preventDefault(); hideLevelSelect(); });
  }
  
  const btnCancelConnection = document.getElementById('btnCancelConnection');
  if (btnCancelConnection) {
    const cancelConnHandler = () => {
      const modal = document.getElementById('connectionErrorModal');
      if (modal) modal.classList.remove('active');
      showScreen('menuScreen');
    };
    btnCancelConnection.addEventListener('click', cancelConnHandler);
    btnCancelConnection.addEventListener('touchend', (e) => {
      e.preventDefault();
      cancelConnHandler();
    });
  }
  
  const fileInput = document.getElementById('fileInput');
  if (fileInput) {
    fileInput.addEventListener('change', loadDataFile);
  }
  
  setupTouchControls();
  
  document.addEventListener('touchmove', (e) => {
    if (e.target.tagName !== 'INPUT' && e.target.tagName !== 'TEXTAREA') {
      e.preventDefault();
    }
  }, { passive: false });
  
  let lastTouchEnd = 0;
  document.addEventListener('touchend', (e) => {
    const now = Date.now();
    if (now - lastTouchEnd <= 300) {
      e.preventDefault();
    }
    lastTouchEnd = now;
  }, false);
  
  // タブ閉じる/離脱検知
  window.addEventListener('beforeunload', () => {
    if (isOnline && ws && ws.readyState === WebSocket.OPEN) {
      ws.send(JSON.stringify({ type: 'disconnect' }));
    }
  });
});

// ========== キー設定 ==========
function resetKeys() {
  keys = {
    left: 'ArrowLeft',
    right: 'ArrowRight',
    rotateL: 'z',
    rotateR: 'x',
    softDrop: 'ArrowDown',
    hardDrop: ' ',
    hold: 'c'
  };
  loadKeySettings();
  saveSettings();
  alert('キー設定をリセットしました');
}

// ========== データ管理 ==========
async function loadSettings() {
  try {
    const saved = localStorage.getItem('tetris99_data');
    if (saved) {
      const encryptedData = JSON.parse(saved);
      const data = await verifyData(encryptedData);
      
      if (!data) {
        console.warn('Data verification failed, using defaults');
      } else {
        username = data.username || username;
        highscore = data.highscore || 0;
        rating = data.rating || 1000;
        winStreak = data.winStreak || 0;
        currentRank = getRank(rating);
        serverUrl = data.serverUrl || serverUrl;
        if (data.keys) keys = data.keys;
        
        // タッチ操作設定を復元
        const touchToggle = document.getElementById('touchControlToggle');
        if (touchToggle && data.touchEnabled !== undefined) {
          touchToggle.checked = data.touchEnabled;
          applyTouchSettings();
        }
      }
    }
  } catch(e) {
    console.error('Failed to load settings:', e);
  }
  
  loadKeySettings();
  
  const usernameInput = document.getElementById('usernameInput');
  const serverUrlInput = document.getElementById('serverUrlInput');
  const touchToggle = document.getElementById('touchControlToggle');
  
  if (usernameInput) {
    usernameInput.value = username;
    usernameInput.addEventListener('input', () => {
      username = usernameInput.value || username;
      saveSettings();
      updateUI();
      updateTitleStats();
    });
  }
  if (serverUrlInput) {
    serverUrlInput.value = serverUrl;
    serverUrlInput.addEventListener('input', () => {
      serverUrl = serverUrlInput.value || serverUrl;
      saveSettings();
    });
  }
  
  // タッチ操作トグルのイベントリスナー追加
  if (touchToggle) {
    touchToggle.addEventListener('change', () => {
      applyTouchSettings();
      saveSettings();
    });
  }
}

function loadKeySettings() {
  const inputs = {
    keyLeft: 'left',
    keyRight: 'right',
    keyRotateL: 'rotateL',
    keyRotateR: 'rotateR',
    keySoftDrop: 'softDrop',
    keyHardDrop: 'hardDrop',
    keyHold: 'hold'
  };
  
  for (let [inputId, keyName] of Object.entries(inputs)) {
    const input = document.getElementById(inputId);
    if (input) {
      const displayValue = keys[keyName] === ' ' ? 'Space' : 
                          keys[keyName].startsWith('Arrow') ? keys[keyName].replace('Arrow', '↑→↓←'[['Up','Right','Down','Left'].indexOf(keys[keyName].slice(5))]) :
                          keys[keyName].toUpperCase();
      input.value = displayValue;
      
      input.addEventListener('keydown', (e) => {
        e.preventDefault();
        const key = e.key;
        keys[keyName] = key;
        const newDisplay = key === ' ' ? 'Space' : 
                          key.startsWith('Arrow') ? key.replace('Arrow', '↑→↓←'[['Up','Right','Down','Left'].indexOf(key.slice(5))]) :
                          key.toUpperCase();
        input.value = newDisplay;
        saveSettings();
      });
    }
  }
}

async function saveSettings() {
  const data = {
    username,
    highscore,
    rating,
    winStreak,
    currentRank,
    serverUrl,
    keys,
    touchEnabled: document.getElementById('touchControlToggle')?.checked || false
  };
  
  const encryptedData = await encryptData(data);
  localStorage.setItem('tetris99_data', JSON.stringify(encryptedData));
  updateTitleStats();
}

async function saveData() {
  await saveSettings();
  
  const data = {
    username,
    highscore,
    rating,
    winStreak,
    currentRank,
    serverUrl,
    keys,
    touchEnabled: document.getElementById('touchControlToggle')?.checked || false
  };
  
  const encryptedData = await encryptData(data);
  const blob = new Blob([JSON.stringify(encryptedData)], {type: 'application/octet-stream'});
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = 'tetris99_save.dat';
  a.click();
  URL.revokeObjectURL(url);
  alert('データを保存しました');
}

async function loadDataFile(e) {
  const file = e.target.files[0];
  if (!file) return;
  
  const reader = new FileReader();
  reader.onload = async (event) => {
    try {
      const encryptedData = JSON.parse(event.target.result);
      const data = await verifyData(encryptedData);
      
      if (!data) {
        alert('データが改ざんされています。読み込みを中止します。');
        return;
      }
      
      username = data.username || username;
      highscore = data.highscore || 0;
      rating = data.rating || 1000;
      winStreak = data.winStreak || 0;
      currentRank = getRank(rating);
      serverUrl = data.serverUrl || serverUrl;
      if (data.keys) keys = data.keys;
      
      // タッチ操作設定も復元
      const touchToggle = document.getElementById('touchControlToggle');
      if (touchToggle && data.touchEnabled !== undefined) {
        touchToggle.checked = data.touchEnabled;
        applyTouchSettings();
      }
      
      if (document.getElementById('usernameInput')) {
        document.getElementById('usernameInput').value = username;
      }
      if (document.getElementById('serverUrlInput')) {
        document.getElementById('serverUrlInput').value = serverUrl;
      }
      
      loadKeySettings();
      await saveSettings();
      updateUI();
      updateTitleStats();
      alert('データを読み込みました');
    } catch(e) {
      alert('データの読み込みに失敗しました');
    }
  };
  reader.readAsText(file);
  e.target.value = '';
}

// ========== ゲームモード開始 ==========
function startWithLevel(level) {
  cpuLevel = level;
  hideLevelSelect();
  if (pendingMode === 'single') {
    startSinglePlayer();
  } else if (pendingMode === 'cpu1v1') {
    startCPU1v1();
  }
}

function startSinglePlayer() {
  console.log('startSinglePlayer called');
  saveSettings();
  gameMode = 'single';
  isOnline = false;
  cpuOpponent = null;
  if (cpuIntervalId) { clearInterval(cpuIntervalId); cpuIntervalId = null; }
  showScreen('gameScreen');
  applyTouchSettings();
  
  const lp = document.getElementById('leftPanel');
  const rp = document.getElementById('rightPanel');
  const cp = document.getElementById('cpuPanel');
  const pb = document.getElementById('pauseBtn');
  const lpg = document.getElementById('leftPlayersGrid');
  const mga = document.getElementById('mainGameArea');
  if (lp) lp.style.display = 'none';
  if (rp) rp.style.display = 'none';
  if (cp) cp.style.display = 'none';
  if (pb) pb.style.display = 'block';
  if (lpg) lpg.style.display = '';
  // シングルは中央配置に戻す
  if (mga) {
    mga.style.left = '50%';
    mga.style.right = 'auto';
    mga.style.transform = 'translate(-50%, -50%)';
    mga.style.top = '50%';
  }
  
  initGameState();
  startCountdown();
}

function startCPU1v1() {
  console.log('startCPU1v1 called');
  saveSettings();
  gameMode = 'cpu1v1';
  isOnline = false;
  if (cpuIntervalId) { clearInterval(cpuIntervalId); cpuIntervalId = null; }
  cpuOpponent = null;
  showScreen('gameScreen');
  applyTouchSettings();
  
  // CPU1v1: 左にCPU、右にプレイヤー（間隔を近く）
  const lp = document.getElementById('leftPanel');
  const rp = document.getElementById('rightPanel');
  const cp = document.getElementById('cpuPanel');
  const pb = document.getElementById('pauseBtn');
  const lpg = document.getElementById('leftPlayersGrid');
  const mga = document.getElementById('mainGameArea');
  
  if (lp) {
    lp.style.display = '';
    lp.style.left = 'calc(50% - 270px)'; // CPU(240px) + 余白(30px)
  }
  if (rp) rp.style.display = 'none';
  if (cp) cp.style.display = 'block';
  if (pb) pb.style.display = 'block';
  if (lpg) lpg.style.display = 'none';
  
  // プレイヤーフィールドを右寄りに（CPUとの距離30px）
  if (mga) {
    mga.style.left = 'calc(50% + 30px)'; // CPUとの間隔30px
    mga.style.right = 'auto';
    mga.style.transform = 'translate(-50%, -50%)';
    mga.style.top = '50%';
  }
  
  // CPU level表示
  const lvEl = document.getElementById('cpuLevelValue');
  if (lvEl) lvEl.textContent = currentRank;
  
  initGameState();
  startCPUOpponent();
  startCountdown();
}

// ======= CPUローカルAI =======
const CPU_SHAPES = {
  I:[[0,0,0,0],[1,1,1,1],[0,0,0,0],[0,0,0,0]],
  J:[[1,0,0],[1,1,1],[0,0,0]],
  L:[[0,0,1],[1,1,1],[0,0,0]],
  O:[[1,1],[1,1]],
  S:[[0,1,1],[1,1,0],[0,0,0]],
  T:[[0,1,0],[1,1,1],[0,0,0]],
  Z:[[1,1,0],[0,1,1],[0,0,0]]
};
const CPU_COLORS = {I:'#0ff',J:'#00f',L:'#f80',O:'#ff0',S:'#0f0',T:'#a0f',Z:'#f00'};

function startCPUOpponent() {
  if (cpuIntervalId) clearInterval(cpuIntervalId);
  
  const cpuField = Array.from({length:20}, () => Array(10).fill(""));
  const cpuBag = [];
  let cpuCurrent = null;
  let cpuScore = 0;
  
  function cpuRefillBag() {
    const types = ['I','J','L','O','S','T','Z'];
    types.sort(() => Math.random()-0.5);
    cpuBag.push(...types);
  }
  
  function cpuGetPiece() {
    if (!cpuBag.length) cpuRefillBag();
    const type = cpuBag.pop();
    return { type, shape: JSON.parse(JSON.stringify(CPU_SHAPES[type])), color: CPU_COLORS[type], x: 3, y: 0 };
  }
  
  function cpuCollision(x, y, shape) {
    for (let r = 0; r < shape.length; r++)
      for (let c = 0; c < shape[r].length; c++)
        if (shape[r][c]) {
          const nx = x+c, ny = y+r;
          if (nx<0||nx>=10||ny>=20) return true;
          if (ny>=0 && cpuField[ny][nx]) return true;
        }
    return false;
  }
  
  function cpuRotate(shape) {
    const R = shape.length, C = shape[0].length;
    const out = Array.from({length:C}, () => Array(R).fill(0));
    for (let r=0;r<R;r++) for (let c=0;c<C;c++) out[c][R-1-r] = shape[r][c];
    return out;
  }
  
  function cpuEval(x, y, shape, level) {
    const test = cpuField.map(r => [...r]);
    for (let r=0;r<shape.length;r++)
      for (let c=0;c<shape[r].length;c++)
        if (shape[r][c]) { const ny=y+r,nx=x+c; if(ny>=0&&ny<20&&nx>=0&&nx<10) test[ny][nx]='X'; }
    
    // ライン消去数
    let lines = 0;
    for (let row=0;row<20;row++) if (test[row].every(c=>c)) lines++;
    
    // 穴の数（より厳密に）
    let holes = 0;
    for (let col=0;col<10;col++) {
      let blockFound = false;
      for (let row=0;row<20;row++) {
        if (test[row][col]) blockFound = true;
        else if (blockFound) holes++;
      }
    }
    
    // 最大高さと平均高さ
    let heights = [];
    for (let col=0;col<10;col++) {
      let h = 0;
      for (let row=0;row<20;row++) {
        if (test[row][col]) { h = 20-row; break; }
      }
      heights.push(h);
    }
    const maxH = Math.max(...heights);
    const avgH = heights.reduce((a,b)=>a+b,0) / 10;
    
    // 凹凸（高さの差の合計）
    let bumpiness = 0;
    for (let i=0;i<9;i++) bumpiness += Math.abs(heights[i] - heights[i+1]);
    
    // 井戸（深い凹み）の検出
    let wells = 0;
    for (let col=1;col<9;col++) {
      const depth = Math.min(heights[col-1], heights[col+1]) - heights[col];
      if (depth >= 3) wells += depth;
    }
    
    // 【強化1】4ライン同時消しの検出
    let tetrisBonus = 0;
    if (lines === 4) tetrisBonus = 1000; // 大ボーナス
    
    // 【強化2】連鎖準備（次のライン消去がしやすい状態）
    let almostFullLines = 0;
    for (let row=0;row<20;row++) {
      const filled = test[row].filter(c=>c).length;
      if (filled >= 8) almostFullLines++; // 8マス以上埋まっている行
    }
    
    // 【強化3】壁際利用ボーナス（IピースやLピースを壁際に置くと有利）
    let wallBonus = 0;
    if (x === 0 || x + shape[0].length === 10) wallBonus = 20;
    
    // 【強化4】列の高さバランス（平坦を好む）
    let flatBonus = 0;
    const heightDiff = Math.max(...heights) - Math.min(...heights);
    flatBonus = -heightDiff * 3;
    
    // レベル別のウェイト調整（全体的に強化）
    let holeWeight = 70, bumpWeight = 8, heightWeight = 15, lineWeight = 300;
    if (level === 1) {
      // Lv1: 超弱 - ほぼランダム
      holeWeight = 10; bumpWeight = 1; heightWeight = 2; lineWeight = 50;
    } else if (level === 2) {
      // Lv2: 弱 - 穴を少し避ける程度
      holeWeight = 30; bumpWeight = 3; heightWeight = 6; lineWeight = 120;
    } else if (level === 3) {
      // Lv3: 普通 - バランス型（強化）
      holeWeight = 50; bumpWeight = 5; heightWeight = 10; lineWeight = 200;
    } else if (level === 4) {
      // Lv4: 強 - 穴と凹凸を強く避ける
      holeWeight = 80; bumpWeight = 10; heightWeight = 15; lineWeight = 350;
    } else if (level === 5) {
      // Lv5: 超強 - 最適化重視＋攻撃的
      holeWeight = 120; bumpWeight = 15; heightWeight = 20; lineWeight = 500;
      wells *= 30; // 井戸を絶対避ける
      tetrisBonus *= 1.5; // 4ラインをさらに重視
    } else {
      // ランクマッチ: currentRankに応じて（全体的に強化）
      const rankWeights = {
        'F': 20, 'E': 35, 'D': 50, 'C': 65, 'B': 80, 'A': 95, 'S': 110, 'S+': 130, 'S++': 160
      };
      holeWeight = rankWeights[currentRank] || 70;
      bumpWeight = holeWeight / 7;
      heightWeight = holeWeight / 3.5;
      lineWeight = holeWeight * 5;
      
      // S以上は4ラインとほぼ満杯ラインをさらに重視
      if (currentRank === 'S' || currentRank === 'S+' || currentRank === 'S++') {
        tetrisBonus *= 1.5;
        almostFullLines *= 1.5;
      }
    }
    
    let score = 0;
    score += lines * lineWeight;
    score += tetrisBonus; // 4ライン大ボーナス
    score += almostFullLines * 30; // 連鎖準備ボーナス
    score += wallBonus; // 壁際ボーナス
    score += flatBonus; // 平坦ボーナス
    score -= holes * holeWeight;
    score -= bumpiness * bumpWeight;
    score -= maxH * heightWeight;
    score -= avgH * (heightWeight / 2);
    score -= wells * 20;
    score -= y * 2; // より低い位置を優先（強化）
    
    return score;
  }
  
  function cpuBestMove(piece, level) {
    let best = -Infinity, bestX=piece.x, bestShape=piece.shape;
    for (let rot=0;rot<4;rot++) {
      let sh = JSON.parse(JSON.stringify(piece.shape));
      for (let i=0;i<rot;i++) sh = cpuRotate(sh);
      for (let x=-2;x<10;x++) {
        let y=0;
        while (!cpuCollision(x,y+1,sh)) y++;
        if (cpuCollision(x,y,sh)) continue;
        const s = cpuEval(x,y,sh,level);
        if (s>best) { best=s; bestX=x; bestShape=sh; }
      }
    }
    return { x: bestX, shape: bestShape };
  }
  
  function cpuMerge(x, y, shape, color) {
    for (let r=0;r<shape.length;r++) for (let c=0;c<shape[r].length;c++)
      if (shape[r][c]) { const ny=y+r,nx=x+c; if(ny>=0&&ny<20) cpuField[ny][nx]=color; }
  }
  
  function cpuClear() {
    let cleared = 0;
    for (let y=19;y>=0;y--) {
      if (cpuField[y].every(c=>c)) { cpuField.splice(y,1); cpuField.unshift(Array(10).fill("")); cleared++; y++; }
    }
    return cleared;
  }
  
  function cpuReceiveGarbage(lines) {
    for (let i=0;i<lines;i++) {
      cpuField.shift();
      const hole = Math.floor(Math.random()*10);
      const row = Array(10).fill('#808080');
      row[hole] = "";
      cpuField.push(row);
    }
  }
  
  cpuOpponent = { isAlive: true, field: cpuField, score: 0, currentPiece: null, nextType: null, receiveGarbage: cpuReceiveGarbage };
  
  // 難易度：レベル/ランクに応じたCPU速度（1ピース配置までの時間）
  let speed;
  if (cpuLevel !== null) {
    // 練習モード：レベル1-5
    const levelSpeeds = {
      1: 3500,  // Lv1: 3.5秒/手（初心者）
      2: 2500,  // Lv2: 2.5秒/手
      3: 1800,  // Lv3: 1.8秒/手
      4: 1200,  // Lv4: 1.2秒/手（強い）
      5: 700    // Lv5: 0.7秒/手（超強い、ほぼプロ級）
    };
    speed = levelSpeeds[cpuLevel] || 2000;
  } else {
    // ランクマッチ：プレイヤーのランクに応じて
    const rankSpeeds = {
      'F': 3500,    // 3.5秒/手
      'E': 2800,    // 2.8秒/手
      'D': 2200,    // 2.2秒/手
      'C': 1700,    // 1.7秒/手
      'B': 1300,    // 1.3秒/手
      'A': 1000,    // 1.0秒/手
      'S': 750,     // 0.75秒/手（速い）
      'S+': 500,    // 0.5秒/手（超速）
      'S++': 350    // 0.35秒/手（最速、人間では不可能な領域）
    };
    speed = rankSpeeds[currentRank] || 1700;
  }
  
  cpuCurrent = cpuGetPiece();
  let cpuNext = cpuGetPiece();
  cpuOpponent.nextType = cpuNext.type;
  
  // 最適な配置先を計算（アニメーション用）
  let cpuTargetX = cpuCurrent.x;
  let cpuTargetShape = cpuCurrent.shape;
  let cpuDropY = 0;
  let cpuAnimX = cpuCurrent.x;
  let cpuAnimY = 0;
  let cpuAnimStep = 0;
  
  function calcTarget(piece) {
    const move = cpuBestMove(piece, cpuLevel);
    let dy = 0;
    while (!cpuCollision(move.x, dy+1, move.shape)) dy++;
    return { x: move.x, shape: move.shape, dropY: dy };
  }
  
  // ターゲット計算（待機中）
  let target = null;
  
  // アニメーションループ（requestAnimationFrame）
  let lastCPUTime = 0;
  let cpuStepInterval = speed / 30; // 1手を30分割してアニメーション
  let cpuStarted = false; // プレイヤーがスタートするまで待機
  
  function cpuAnimate(time) {
    if (!cpuOpponent || !cpuOpponent.isAlive || gameOver) return;
    if (isPaused) { requestAnimationFrame(cpuAnimate); return; }
    
    // プレイヤーがスタートするまで待機
    if (!cpuStarted) {
      if (!current) { requestAnimationFrame(cpuAnimate); return; }
      cpuStarted = true;
      lastCPUTime = time;
      target = calcTarget(cpuCurrent);
      cpuAnimX = cpuCurrent.x;
      cpuAnimY = 0;
      cpuAnimStep = 0;
    }
    
    const dt = time - lastCPUTime;
    if (dt >= cpuStepInterval) {
      lastCPUTime = time;
      cpuAnimStep++;
      
      // X方向に1マス移動
      if (cpuAnimX !== target.x) {
        cpuAnimX += cpuAnimX < target.x ? 1 : -1;
      }
      // Y方向に1マス落下
      if (cpuAnimY < target.dropY) {
        cpuAnimY++;
      }
      
      // 現在ピースを更新（描画用）
      cpuOpponent.currentPiece = {
        shape: target.shape,
        color: cpuCurrent.color,
        x: cpuAnimX,
        y: cpuAnimY
      };
      
      // ターゲットに到達したらピースを配置
      if (cpuAnimX === target.x && cpuAnimY === target.dropY) {
        cpuMerge(target.x, target.dropY, target.shape, cpuCurrent.color);
        const cleared = cpuClear();
        cpuOpponent.score += [0,100,300,500,800][cleared] || 0;
        cpuOpponent.field = cpuField;
        cpuOpponent.currentPiece = null;
        
        if (cleared >= 1) {
          // 1ライン以上で攻撃（強化）
          let attackLines = 0;
          if (cleared === 1) attackLines = 0; // 1ラインは攻撃なし（弱すぎるので）
          else if (cleared === 2) attackLines = 1;
          else if (cleared === 3) attackLines = 2;
          else if (cleared === 4) attackLines = 4; // 4ラインで4攻撃
          
          if (attackLines > 0) {
            handleAttackFromCPU(attackLines);
          }
        }
        
        // 次のピースへ
        cpuCurrent = cpuNext;
        cpuNext = cpuGetPiece();
        cpuOpponent.nextType = cpuNext.type;
        
        if (cpuCollision(cpuCurrent.x, cpuCurrent.y, cpuCurrent.shape)) {
          cpuOpponent.isAlive = false;
          cpuOpponent.currentPiece = null;
          if (!gameOver) endCPU1v1(true);
          return;
        }
        
        target = calcTarget(cpuCurrent);
        cpuAnimX = cpuCurrent.x;
        cpuAnimY = 0;
        cpuAnimStep = 0;
      }
    }
    
    drawCPUField();
    requestAnimationFrame(cpuAnimate);
  }
  
  requestAnimationFrame(cpuAnimate);
}

function handleAttackFromCPU(lines) {
  // ゴミラインを自分のフィールドに追加
  for (let i=0;i<lines;i++) {
    field.shift();
    const hole = Math.floor(Math.random()*10);
    const row = Array(10).fill('#808080');
    row[hole] = "";
    field.push(row);
  }
  showIndicator('attackIndicator', `💥 CPU ATTACK ${lines}L`);
}

function endCPU1v1(playerWon) {
  const position = playerWon ? 1 : 2;
  const ratingResult = updateRating(position, 2);
  updateTitleStats();
  gameOver = true;
  current = null;
  showGameOverModal(ratingResult);
}

// CPUフィールドを本物のテトリスと同じように描画
function drawCPUField() {
  if (!cpuOpponent) return;
  const cvs = document.getElementById('cpuCanvas');
  if (!cvs) return;
  const c = cvs.getContext('2d');
  const BW = cvs.width / 10;   // 24px
  const BH = cvs.height / 20;  // 24px

  // 背景
  c.fillStyle = '#000';
  c.fillRect(0, 0, cvs.width, cvs.height);

  // グリッド
  c.strokeStyle = 'rgba(255,255,255,0.05)';
  c.lineWidth = 0.5;
  for (let x = 0; x <= 10; x++) { c.beginPath(); c.moveTo(x*BW,0); c.lineTo(x*BW,cvs.height); c.stroke(); }
  for (let y = 0; y <= 20; y++) { c.beginPath(); c.moveTo(0,y*BH); c.lineTo(cvs.width,y*BH); c.stroke(); }

  // フィールド描画
  for (let y = 0; y < 20; y++) {
    for (let x = 0; x < 10; x++) {
      const col = cpuOpponent.field[y][x];
      if (col) drawCPUBlock(c, x, y, col, BW, BH);
    }
  }

  // 現在のピース（アニメーション）
  if (cpuOpponent.currentPiece) {
    const p = cpuOpponent.currentPiece;
    // ゴーストピース
    let ghostY = p.y;
    while (!cpuFieldCollision(p.x, ghostY + 1, p.shape, cpuOpponent.field)) ghostY++;
    if (ghostY !== p.y) {
      c.globalAlpha = 0.25;
      for (let ry = 0; ry < p.shape.length; ry++)
        for (let rx = 0; rx < p.shape[ry].length; rx++)
          if (p.shape[ry][rx]) drawCPUBlock(c, p.x+rx, ghostY+ry, p.color, BW, BH);
      c.globalAlpha = 1.0;
    }
    // 実ピース
    for (let ry = 0; ry < p.shape.length; ry++)
      for (let rx = 0; rx < p.shape[ry].length; rx++)
        if (p.shape[ry][rx]) drawCPUBlock(c, p.x+rx, p.y+ry, p.color, BW, BH);
  }

  // スコア表示
  const scoreEl = document.getElementById('cpuScoreValue');
  if (scoreEl) scoreEl.textContent = cpuOpponent.score.toLocaleString();
  
  // ステータス表示
  const statusEl = document.getElementById('cpuStatusValue');
  if (statusEl) {
    if (!cpuOpponent.isAlive) {
      statusEl.textContent = 'DEAD';
      statusEl.style.color = '#f00';
    } else {
      statusEl.textContent = 'PLAYING';
      statusEl.style.color = '#0f0';
    }
  }

  // NEXTキャンバス描画
  const nCvs = document.getElementById('cpuNextCanvas');
  if (nCvs && cpuOpponent.nextType) {
    try {
      const nc = nCvs.getContext('2d');
      nc.clearRect(0, 0, nCvs.width, nCvs.height);
      
      const shape = CPU_SHAPES[cpuOpponent.nextType];
      const color = CPU_COLORS[cpuOpponent.nextType];
      
      if (!shape || !color) {
        console.error('Invalid CPU next type:', cpuOpponent.nextType);
        return;
      }
      
      // サイズ計算（プレイヤーと同じロジック）
      const sz = Math.floor(Math.min(nCvs.width / (shape[0].length + 1), nCvs.height / (shape.length + 1)));
      const ox = (nCvs.width - shape[0].length * sz) / 2;
      const oy = (nCvs.height - shape.length * sz) / 2;
      
      for (let ry = 0; ry < shape.length; ry++) {
        for (let rx = 0; rx < shape[ry].length; rx++) {
          if (shape[ry][rx]) {
            const px = ox + rx * sz;
            const py = oy + ry * sz;
            const grad = nc.createLinearGradient(px, py, px + sz, py + sz);
            grad.addColorStop(0, '#fff');
            grad.addColorStop(0.3, color);
            grad.addColorStop(1, '#000');
            nc.fillStyle = grad;
            nc.fillRect(px, py, sz, sz);
            nc.strokeStyle = '#fff';
            nc.lineWidth = 0.5;
            nc.strokeRect(px, py, sz, sz);
          }
        }
      }
    } catch (e) {
      console.error('CPU NEXT draw error:', e);
    }
  }
}

function cpuFieldCollision(x, y, shape, field) {
  for (let r = 0; r < shape.length; r++)
    for (let c2 = 0; c2 < shape[r].length; c2++)
      if (shape[r][c2]) {
        const nx = x+c2, ny = y+r;
        if (nx<0||nx>=10||ny>=20) return true;
        if (ny>=0 && field[ny][nx]) return true;
      }
  return false;
}

function drawCPUBlock(c, x, y, color, BW, BH) {
  if (y < 0) return;
  const grad = c.createLinearGradient(x*BW, y*BH, (x+1)*BW, (y+1)*BH);
  grad.addColorStop(0, '#fff');
  grad.addColorStop(0.3, color);
  grad.addColorStop(1, '#000');
  c.fillStyle = grad;
  c.fillRect(x*BW, y*BH, BW, BH);
  c.strokeStyle = '#fff';
  c.lineWidth = 0.5;
  c.strokeRect(x*BW, y*BH, BW, BH);
}

function startOnlineMatch() {
  console.log('Starting online match, username:', username, 'rank:', currentRank);
  saveSettings();
  gameMode = 'online';
  isHost = false;
  
  // リトライカウンターをリセット
  connectionRetries = 0;
  
  connectToServer().then(() => {
    console.log('Connected to server, sending quickMatch');
    ws.send(JSON.stringify({
      type: 'quickMatch',
      username: username,
      rank: currentRank  // レートではなくランクを送信
    }));
    showScreen('waitingScreen');
    document.getElementById('waitingMessage').textContent = `マッチング中... (ランク: ${currentRank})`;
    document.getElementById('roomCodeDisplay').textContent = '';
    document.getElementById('btnStartGame').style.display = 'none';
  }).catch((err) => {
    console.error('Connection failed:', err);
    showConnectionError('サーバーに接続できませんでした');
  });
}

function createRoom() {
  saveSettings();
  const password = document.getElementById('roomPasswordInput')?.value || null;
  const maxPlayers = parseInt(document.getElementById('maxPlayersInput')?.value) || 99;
  
  gameMode = 'private';
  isHost = true;
  
  // リトライカウンターをリセット
  connectionRetries = 0;
  
  connectToServer().then(() => {
    ws.send(JSON.stringify({
      type: 'createRoom',
      username: username,
      password: password,
      maxPlayers: maxPlayers
    }));
  }).catch(() => {
    showConnectionError('サーバーに接続できませんでした');
  });
}

function joinRoom() {
  saveSettings();
  const roomCode = document.getElementById('roomCodeInput').value;
  const password = document.getElementById('joinPasswordInput').value || null;
  
  if (!roomCode) {
    alert('ルームコードを入力してください');
    return;
  }
  
  gameMode = 'private';
  isHost = false;
  
  // リトライカウンターをリセット
  connectionRetries = 0;
  
  connectToServer().then(() => {
    ws.send(JSON.stringify({
      type: 'joinRoom',
      username: username,
      roomId: roomCode,
      password: password
    }));
  }).catch(() => {
    showConnectionError('サーバーに接続できませんでした');
  });
}

function hostStartGame() {
  if (!isHost || !ws) return;
  
  ws.send(JSON.stringify({
    type: 'startGame'
  }));
}

function leaveRoom() {
  if (ws) {
    ws.send(JSON.stringify({ type: 'leaveRoom' }));
    ws.close();
  }
  showScreen('menuScreen');
  isOnline = false;
}

function applyTouchSettings() {
  const touchEnabled = document.getElementById('touchControlToggle')?.checked || false;
  const touchControls = document.getElementById('touchControls');
  if (touchControls) {
    touchControls.style.display = touchEnabled ? 'block' : 'none';
  }
}

// ========== 接続エラー処理 ==========
function showConnectionError(message) {
  const modal = document.getElementById('connectionErrorModal');
  const errorMessage = document.getElementById('errorMessage');
  
  if (errorMessage) errorMessage.textContent = message;
  if (modal) modal.classList.add('active');
}

function retryConnection() {
  document.getElementById('connectionErrorModal').classList.remove('active');
  
  if (gameMode === 'online') {
    startOnlineMatch();
  } else if (gameMode === 'private' && isHost) {
    createRoom();
  } else if (gameMode === 'private') {
    joinRoom();
  }
}

// ========== WebSocket ==========
function connectToServer() {
  return new Promise((resolve, reject) => {
    try {
      let wsUrl = serverUrl;
      if (!wsUrl.startsWith('ws://') && !wsUrl.startsWith('wss://')) {
        wsUrl = 'wss://' + wsUrl.replace(/^https?:\/\//, '');
      }
      wsUrl = wsUrl.replace(/\/$/, '');
      
      console.log('Connecting to:', wsUrl, 'Attempt:', connectionRetries + 1);
      ws = new WebSocket(wsUrl);
      
      ws.onopen = () => {
        console.log('WebSocket connected');
        isOnline = true;
        connectionRetries = 0;
      };
      
      ws.onmessage = (event) => {
        try {
          const data = JSON.parse(event.data);
          handleServerMessage(data);
        } catch(e) {
          console.error('Message parse error:', e);
        }
      };
      
      ws.onclose = (event) => {
        console.log('WebSocket disconnected:', event.code, event.reason);
        isOnline = false;
        if (matchTimer) {
          clearInterval(matchTimer);
          matchTimer = null;
        }
        
        // 切断検知 - 実際にゲームプレイ中なら負け判定
        // ゲーム画面が表示されていて、まだゲームオーバーしていない場合のみ
        const gameScreen = document.getElementById('gameScreen');
        if (!gameOver && gameMode !== 'single' && gameScreen && gameScreen.classList.contains('active')) {
          console.log('Disconnected during game - marking as loss');
          endGame(true);
        }
      };
      
      ws.onerror = (error) => {
        console.error('WebSocket error:', error);
        
        if (connectionRetries < maxRetries) {
          connectionRetries++;
          console.log(`Retrying connection... (${connectionRetries}/${maxRetries})`);
          
          // 待機画面にリトライメッセージを表示
          const waitingMessage = document.getElementById('waitingMessage');
          if (waitingMessage) {
            waitingMessage.textContent = `接続中... (${connectionRetries}/${maxRetries})`;
          }
          
          if (retryTimeout) clearTimeout(retryTimeout);
          retryTimeout = setTimeout(() => {
            connectToServer().then(resolve).catch(reject);
          }, 2000 * connectionRetries);
        } else {
          // リトライ上限に達した
          const waitingMessage = document.getElementById('waitingMessage');
          if (waitingMessage) {
            waitingMessage.textContent = '接続に失敗しました';
          }
          reject(new Error('Connection failed after ' + maxRetries + ' attempts'));
        }
      };
      
      const checkConn = (event) => {
        try {
          const data = JSON.parse(event.data);
          if (data.type === 'connected') {
            clientId = data.clientId;
            console.log('Client ID:', clientId);
            ws.removeEventListener('message', checkConn);
            resolve();
          }
        } catch(e) {
          console.error('Connection check error:', e);
        }
      };
      ws.addEventListener('message', checkConn);
      
      setTimeout(() => {
        if (!clientId) {
          ws.close();
          reject(new Error('Connection timeout'));
        }
      }, 10000);
    } catch(e) {
      console.error('WebSocket creation error:', e);
      reject(e);
    }
  });
}

function handleServerMessage(data) {
  console.log('Server message:', data.type);
  
  switch(data.type) {
    case 'roomCreated':
      roomId = data.roomId;
      showScreen('waitingScreen');
      document.getElementById('waitingMessage').textContent = 'プレイヤーを待っています';
      document.getElementById('roomCodeDisplay').textContent = `ルームコード: ${roomId}`;
      document.getElementById('btnStartGame').style.display = 'block';
      hideAllPanels();
      break;
      
    case 'roomJoined':
      roomId = data.roomId;
      updatePlayersList(data.players);
      showScreen('waitingScreen');
      document.getElementById('waitingMessage').textContent = 'ゲーム開始を待っています';
      document.getElementById('roomCodeDisplay').textContent = `ルームコード: ${roomId}`;
      document.getElementById('btnStartGame').style.display = 'none';
      hideAllPanels();
      break;
      
    case 'quickMatchFound':
      roomId = data.roomId;
      console.log('Match found with', data.players ? data.players.length : 0, 'players');
      updatePlayersList(data.players);
      
      // マッチング完了メッセージを更新
      const waitingMessage = document.getElementById('waitingMessage');
      if (waitingMessage) {
        waitingMessage.textContent = `マッチング完了！プレイヤー: ${data.players ? data.players.length : 0}人`;
      }
      
      startMatchTimer();
      break;
      
    case 'playerJoined':
      console.log('Player joined:', data);
      if (data.players) {
        updatePlayersList(data.players);
        // ゲーム中なら新しいプレイヤーのミニフィールドも追加
        const gameScreen = document.getElementById('gameScreen');
        if (gameScreen && gameScreen.classList.contains('active')) {
          updateOnlinePlayers(data.players);
        }
      }
      break;
      
    case 'playerLeft':
    case 'playerDisconnected':
      console.log('Player left/disconnected:', data);
      if (data.players) {
        updatePlayersList(data.players);
      }
      if (data.playerId) {
        markPlayerDead(data.playerId);
        const playerData = allPlayersData.get(data.playerId);
        if (playerData) {
          playerData.isAlive = false;
        }
        // 全員死亡チェック
        checkAllPlayersDead();
      }
      break;
      
    case 'gameStart':
      console.log('Game starting! Timer was at:', matchTimeLeft, 'seconds');
      if (matchTimer) { clearInterval(matchTimer); matchTimer = null; }
      document.getElementById('matchTimer')?.style.setProperty('display', 'none');
      
      isOnline = true; // プライベートでも確実にtrueにする
      
      if (data.players) {
        allPlayersData.clear();
        data.players.forEach(p => {
          allPlayersData.set(p.id, { id: p.id, name: p.name || 'Player', score: 0, isAlive: true });
        });
      }
      
      updateOnlinePlayers(data.players);
      showScreen('gameScreen');
      applyTouchSettings();
      
      // ポーズ非表示（プライベートマッチはポーズ不可）
      const pauseBtn = document.getElementById('pauseBtn');
      if (pauseBtn) pauseBtn.style.display = 'none';
      
      field = Array.from({length: ROWS}, () => Array(COLS).fill(""));
      score = 0; combo = -1; backToBack = false; totalLinesCleared = 0;
      heldPiece = null; canHold = true; gameOver = false; gameEndHandled = false;
      isPaused = false; lockDelay = 0; moveResets = 0; bag = []; dropCounter = 0;
      rotationState = 0; isSpectating = false; lastFieldUpdate = 0;
      
      nextPiece = getNextPiece();
      startCountdown();
      break;
      
    case 'playerUpdate':
      updatePlayerField(data);
      const playerData = allPlayersData.get(data.playerId);
      if (playerData && data.score !== undefined) {
        playerData.score = data.score;
      }
      if (isSpectating) {
        const player = spectatingPlayers.find(p => p.id === data.playerId);
        if (player && data.field) {
          player.field = data.field;
          player.score = data.score || 0;
          player.currentPiece = data.currentPiece;
          if (player.id === spectatingPlayers[spectateIndex]?.id) {
            updateSpectateView();
          }
        }
      }
      break;
      
    case 'playerDied':
      markPlayerDead(data.playerId);
      const deadPlayer = allPlayersData.get(data.playerId);
      if (deadPlayer) {
        deadPlayer.isAlive = false;
        deadPlayer.score = data.score || deadPlayer.score || 0;
      }
      checkAllPlayersDead();
      break;
      
    case 'gameEnd':
      handleGameEnd(data);
      break;
      
    case 'attacked':
      if (!gameOver && !isSpectating) {
        handleAttack(data);
      }
      break;
      
    case 'chat':
      if (data.message && data.username) {
        addChatMessage(data.username, data.message);
        // プレイ中でも通知を表示
        showChatNotification(data.username, data.message);
      }
      break;
      
    case 'error':
      console.error('Server error:', data.message);
      alert(data.message || 'エラーが発生しました');
      
      // 待機画面からメニューに戻る
      const waitingScreen = document.getElementById('waitingScreen');
      if (waitingScreen && waitingScreen.classList.contains('active')) {
        showScreen('menuScreen');
      }
      break;
  }
}

function startMatchTimer() {
  matchTimeLeft = 60;
  const timerDisplay = document.getElementById('matchTimer');
  const timerValue = document.getElementById('timerValue');
  
  console.log('Starting match timer: 60 seconds');
  
  if (timerDisplay) {
    timerDisplay.style.display = 'block';
  }
  
  if (matchTimer) {
    clearInterval(matchTimer);
  }
  
  matchTimer = setInterval(() => {
    matchTimeLeft--;
    if (timerValue) {
      timerValue.textContent = matchTimeLeft;
    }
    
    if (matchTimeLeft % 10 === 0) {
      console.log('Match timer:', matchTimeLeft, 'seconds remaining');
    }
    
    if (matchTimeLeft <= 0) {
      console.log('Match timer expired, sending forceStart');
      clearInterval(matchTimer);
      matchTimer = null;
      if (ws && ws.readyState === WebSocket.OPEN) {
        ws.send(JSON.stringify({ type: 'forceStart' }));
      }
    }
  }, 1000);
}

function updatePlayersList(players) {
  const list = document.getElementById('playersList');
  if (!list) return;
  
  console.log('Updating players list:', players);
  
  list.innerHTML = '<h3 style="color:#0ff;margin-bottom:15px;">参加プレイヤー (' + players.length + '人)</h3>' +
    players.map(p => {
      const displayName = p.name || 'Player';
      const isMe = p.id === clientId;
      return `<div class="player-item" style="${isMe ? 'border-color: #0ff; box-shadow: 0 0 10px rgba(0,255,255,0.5);' : ''}">
        ${isMe ? '👤 ' : '🎮 '}${displayName}${isMe ? ' (あなた)' : ''}
      </div>`;
    }).join('');
}

function updateOnlinePlayers(players) {
  console.log('Setting up online players:', players);
  
  onlinePlayers.clear();
  miniCanvases.clear();
  
  const leftGrid = document.getElementById('leftPlayersGrid');
  const rightGrid = document.getElementById('rightPlayersGrid');
  
  if (!leftGrid || !rightGrid) {
    console.error('Player grids not found');
    return;
  }
  
  leftGrid.innerHTML = '';
  rightGrid.innerHTML = '';
  
  const otherPlayers = players.filter(p => p.id !== clientId);
  const halfPoint = Math.ceil(otherPlayers.length / 2);
  
  otherPlayers.forEach((player, index) => {
    player.isDead = false;
    player.field = Array.from({length: 20}, () => Array(10).fill(""));
    player.name = player.name || 'Player';
    player.isCPU = player.isCPU || false;
    onlinePlayers.set(player.id, player);
    
    allPlayersData.set(player.id, {
      id: player.id,
      name: player.name,
      score: 0,
      isAlive: true,
      isCPU: player.isCPU
    });
    
    const miniField = document.createElement('div');
    miniField.className = 'mini-field' + (player.isCPU ? ' cpu' : '');
    miniField.id = 'player-' + player.id;
    
    const miniCanvas = document.createElement('canvas');
    miniCanvas.width = 100;
    miniCanvas.height = 200;
    miniCanvases.set(player.id, miniCanvas);
    
    const playerName = document.createElement('div');
    playerName.className = 'player-name';
    playerName.textContent = player.name;
    
    const playerScore = document.createElement('div');
    playerScore.className = 'player-score';
    playerScore.id = 'score-' + player.id;
    playerScore.textContent = '0';
    
    miniField.appendChild(playerName);
    miniField.appendChild(miniCanvas);
    miniField.appendChild(playerScore);
    
    // 左右に振り分け
    if (index < halfPoint) {
      leftGrid.appendChild(miniField);
    } else {
      rightGrid.appendChild(miniField);
    }
  });
  
  console.log('Online players setup complete:', onlinePlayers.size, 'Left:', halfPoint, 'Right:', otherPlayers.length - halfPoint);
}

function updatePlayerField(data) {
  const canvas = miniCanvases.get(data.playerId);
  if (!canvas || !data.field) {
    if (!canvas) console.log('Canvas not found for player:', data.playerId);
    if (!data.field) console.log('Field not provided for player:', data.playerId);
    return;
  }
  
  const player = onlinePlayers.get(data.playerId);
  if (player) {
    player.field = data.field;
    player.currentPiece = data.currentPiece;
    if (data.score !== undefined) {
      player.score = data.score;
    }
  }
  
  // スコア表示を更新
  const scoreElem = document.getElementById('score-' + data.playerId);
  if (scoreElem && data.score !== undefined) {
    scoreElem.textContent = data.score.toLocaleString();
  }
  
  const ctx = canvas.getContext('2d');
  const blockSize = 10;
  
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  
  // フィールド描画
  let blocksDrawn = 0;
  for (let y = 0; y < 20; y++) {
    for (let x = 0; x < 10; x++) {
      if (data.field[y] && data.field[y][x]) {
        ctx.fillStyle = data.field[y][x];
        ctx.fillRect(x * blockSize, y * blockSize, blockSize, blockSize);
        ctx.strokeStyle = '#333';
        ctx.lineWidth = 0.5;
        ctx.strokeRect(x * blockSize, y * blockSize, blockSize, blockSize);
        blocksDrawn++;
      }
    }
  }
  
  // カレントピース描画
  if (data.currentPiece && data.currentPiece.shape && data.currentPiece.x !== undefined && data.currentPiece.y !== undefined) {
    const piece = data.currentPiece;
    ctx.fillStyle = piece.color || '#fff';
    for (let y = 0; y < piece.shape.length; y++) {
      for (let x = 0; x < piece.shape[y].length; x++) {
        if (piece.shape[y][x]) {
          ctx.fillRect((piece.x + x) * blockSize, (piece.y + y) * blockSize, blockSize, blockSize);
          ctx.strokeStyle = '#666';
          ctx.strokeRect((piece.x + x) * blockSize, (piece.y + y) * blockSize, blockSize, blockSize);
        }
      }
    }
  }
}

function markPlayerDead(playerId) {
  const elem = document.getElementById('player-' + playerId);
  if (elem) elem.classList.add('dead');
  
  const player = onlinePlayers.get(playerId);
  if (player) player.isDead = true;
}

function checkAllPlayersDead() {
  if (!isOnline || gameOver) return;
  
  const alivePlayers = Array.from(onlinePlayers.values()).filter(p => !p.isDead);
  console.log('Alive players:', alivePlayers.length, 'Total players:', onlinePlayers.size);
  
  // 自分以外全員死亡、または全員死亡の場合
  if (alivePlayers.length === 0 || (alivePlayers.length === 1 && alivePlayers[0].id === clientId)) {
    console.log('All other players dead, ending game');
    if (ws && ws.readyState === WebSocket.OPEN) {
      ws.send(JSON.stringify({
        type: 'requestGameEnd'  // サーバーにゲーム終了をリクエスト
      }));
    }
  }
}

function handleAttack(data) {
  if (!data || !data.lines) return;
  
  for (let i = 0; i < data.lines; i++) {
    field.shift();
    const garbageLine = Array(COLS).fill("#666");
    const holePos = Math.floor(Math.random() * COLS);
    garbageLine[holePos] = "";
    field.push(garbageLine);
  }
  
  draw();
}

function handleGameEnd(data) {
  console.log('Game end data:', data);
  
  // 重複防止: 既に処理済みなら無視
  if (gameEndHandled) {
    console.log('Game end already handled, ignoring duplicate');
    return;
  }
  
  gameEndHandled = true;
  
  if (!data.rankings || !Array.isArray(data.rankings)) {
    console.error('Invalid ranking data');
    return;
  }
  
  if (clientId) {
    const myData = allPlayersData.get(clientId);
    if (myData) {
      myData.score = score;
      myData.isAlive = !gameOver;
    }
  }
  
  const rankingList = document.getElementById('rankingList');
  if (!rankingList) return;
  
  const rankings = data.rankings.map((player, index) => {
    const playerData = allPlayersData.get(player.id);
    return {
      rank: index + 1,
      id: player.id,
      name: playerData?.name || player.name || 'Player',
      score: playerData?.score || player.score || 0,
      isMe: player.id === clientId
    };
  });
  
  rankingList.innerHTML = '<h3 style="color:#0ff;margin-bottom:15px;">🏆 FINAL RANKING 🏆</h3>' +
    rankings.map(p => `
      <div class="rank-item ${p.isMe ? 'me' : ''}">
        <div class="rank-position">#${p.rank}</div>
        <div class="rank-name">${p.name}</div>
        <div class="rank-score">${p.score.toLocaleString()}</div>
      </div>
    `).join('');
  
  // レート更新（オンライン・プライベート対戦のみ）
  if (gameMode === 'online' || gameMode === 'private') {
    const myRank = rankings.find(p => p.isMe);
    if (myRank) {
      const ratingChange = updateRating(myRank.rank, rankings.length);
      
      const ratingChangeText = document.getElementById('ratingChangeText');
      if (ratingChangeText && ratingChange) {
        const changeSymbol = ratingChange.change >= 0 ? '+' : '';
        const changeColor = ratingChange.change >= 0 ? '#0f0' : '#f00';
        
        let changeHTML = `
          <div style="margin: 20px 0; padding: 20px; background: rgba(0,0,0,0.5); border-radius: 10px;">
            <div style="font-size: 18px; margin-bottom: 10px;">レート変動</div>
            <div style="font-size: 32px; color: ${changeColor}; font-weight: bold; margin: 10px 0;">
              ${changeSymbol}${ratingChange.change}
            </div>
            <div style="font-size: 24px; margin: 10px 0;">
              ${ratingChange.oldRating} → ${rating}
            </div>
        `;
        
        if (ratingChange.oldRank !== ratingChange.newRank) {
          changeHTML += `
            <div style="color: #ffd700; font-size: 20px; margin-top: 15px; animation: glow 1s ease-in-out infinite alternate;">
              🎉 ランクアップ！ ${ratingChange.oldRank} → ${ratingChange.newRank} 🎉
            </div>
          `;
        } else {
          changeHTML += `
            <div style="color: #0ff; font-size: 16px; margin-top: 10px;">
              ランク: ${ratingChange.newRank}
            </div>
          `;
        }
        
        if (myRank.rank === 1) {
          changeHTML += `
            <div style="color: #ffd700; font-size: 18px; margin-top: 10px;">
              🔥 連勝記録: ${winStreak} 🔥
            </div>
          `;
        }
        
        changeHTML += `</div>`;
        ratingChangeText.innerHTML = changeHTML;
      }
    }
  }
  
  if (!gameOver && !isSpectating) {
    setTimeout(() => {
      endGame(true);
    }, 100);
  }
  
  if (isSpectating) {
    exitSpectate();
  }
}

// ========== 観戦モード ==========
function enterSpectateMode() {
  console.log('Entering spectate mode');
  
  if (gameOver && !isSpectating) {
    isSpectating = true;
    spectateIndex = 0;
    
    spectatingPlayers = Array.from(onlinePlayers.entries())
      .filter(([id, p]) => !p.isDead)
      .map(([id, player]) => ({
        id,
        name: player.name || 'Player',
        field: player.field || Array.from({length: 20}, () => Array(10).fill("")),
        currentPiece: player.currentPiece || null,
        score: allPlayersData.get(id)?.score || 0
      }));
    
    console.log('Spectating players:', spectatingPlayers.length);
    
    if (spectatingPlayers.length > 0) {
      document.getElementById('spectateMode').classList.add('active');
      updateSpectateView();
    } else {
      document.getElementById('gameOverModal').classList.add('active');
    }
  }
}

function updateSpectateView() {
  if (spectateIndex < 0 || spectateIndex >= spectatingPlayers.length) return;
  
  const player = spectatingPlayers[spectateIndex];
  const nameDisplay = document.getElementById('spectatePlayerName');
  if (nameDisplay) {
    nameDisplay.textContent = `${player.name} を観戦中 (Score: ${player.score.toLocaleString()})`;
  }
  
  const spectateCanvas = document.getElementById('spectateCanvas');
  if (!spectateCanvas) return;
  
  const ctx = spectateCanvas.getContext('2d');
  ctx.clearRect(0, 0, spectateCanvas.width, spectateCanvas.height);
  const blockSize = 20;
  
  ctx.strokeStyle = "#ffffff22";
  ctx.lineWidth = 1;
  for (let x = 0; x <= 10; x++) {
    ctx.beginPath();
    ctx.moveTo(x * blockSize, 0);
    ctx.lineTo(x * blockSize, 20 * blockSize);
    ctx.stroke();
  }
  for (let y = 0; y <= 20; y++) {
    ctx.beginPath();
    ctx.moveTo(0, y * blockSize);
    ctx.lineTo(10 * blockSize, y * blockSize);
    ctx.stroke();
  }
  
  if (player.field) {
    for (let y = 0; y < 20; y++) {
      for (let x = 0; x < 10; x++) {
        if (player.field[y] && player.field[y][x]) {
          drawSpectateBlock(ctx, x, y, player.field[y][x], blockSize);
        }
      }
    }
  }
  
  if (player.currentPiece && player.currentPiece.shape) {
    const piece = player.currentPiece;
    for (let y = 0; y < piece.shape.length; y++) {
      for (let x = 0; x < piece.shape[y].length; x++) {
        if (piece.shape[y][x]) {
          drawSpectateBlock(ctx, piece.x + x, piece.y + y, piece.color || '#fff', blockSize);
        }
      }
    }
  }
}

function drawSpectateBlock(ctx, x, y, color, size) {
  const grad = ctx.createLinearGradient(
    x * size, y * size,
    (x + 1) * size, (y + 1) * size
  );
  grad.addColorStop(0, "#fff");
  grad.addColorStop(0.3, color);
  grad.addColorStop(1, "#000");
  ctx.fillStyle = grad;
  ctx.fillRect(x * size, y * size, size, size);
  ctx.strokeStyle = "#fff";
  ctx.strokeRect(x * size, y * size, size, size);
}

function exitSpectate() {
  isSpectating = false;
  document.getElementById('spectateMode').classList.remove('active');
  document.getElementById('gameOverModal').classList.add('active');
}

// ========== チャット ==========
function sendChat() {
  const input = document.getElementById('chatInput');
  if (!input || !input.value.trim()) return;
  
  const message = input.value.trim();
  input.value = '';
  
  if (ws && ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify({
      type: 'chat',
      message: message
    }));
  }
  
  addChatMessage(username, message, true);
}

function addChatMessage(user, message, isMe = false) {
  const chatMessages = document.getElementById('chatMessages');
  if (!chatMessages) return;
  
  const msgDiv = document.createElement('div');
  msgDiv.style.marginBottom = '8px';
  msgDiv.style.padding = '5px';
  msgDiv.style.borderRadius = '3px';
  msgDiv.style.backgroundColor = isMe ? 'rgba(102, 126, 234, 0.3)' : 'rgba(255, 255, 255, 0.1)';
  
  const userSpan = document.createElement('span');
  userSpan.style.color = isMe ? '#0ff' : '#ffd700';
  userSpan.style.fontWeight = 'bold';
  userSpan.textContent = user + ': ';
  
  const msgSpan = document.createElement('span');
  msgSpan.textContent = message;
  
  msgDiv.appendChild(userSpan);
  msgDiv.appendChild(msgSpan);
  chatMessages.appendChild(msgDiv);
  
  chatMessages.scrollTop = chatMessages.scrollHeight;
}

function showChatNotification(user, message) {
  const notification = document.getElementById('chatNotification');
  const userElem = document.getElementById('chatNotificationUser');
  const textElem = document.getElementById('chatNotificationText');
  
  if (notification && userElem && textElem) {
    userElem.textContent = user;
    textElem.textContent = message;
    notification.style.display = 'block';
    
    // 3秒後に自動で消す
    setTimeout(() => {
      notification.style.display = 'none';
    }, 3000);
  }
}

// ========== 7-bag ==========
function refillBag() {
  const pieces = ['I','J','L','O','S','T','Z'];
  for (let i = pieces.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [pieces[i], pieces[j]] = [pieces[j], pieces[i]];
  }
  bag.push(...pieces);
}

function getNextPiece() {
  if (bag.length === 0) refillBag();
  return bag.shift();
}

// ========== ゲーム初期化 ==========
function startCountdown() {
  const cd = document.getElementById('countdown');
  if (!cd) return;
  
  let count = 3;
  cd.textContent = count;
  cd.classList.add('active');
  
  const interval = setInterval(() => {
    count--;
    if (count > 0) {
      cd.textContent = count;
    } else {
      cd.textContent = 'START!';
      setTimeout(() => {
        cd.classList.remove('active');
        initGame();
      }, 500);
      clearInterval(interval);
    }
  }, 1000);
}

function initGame() {
  spawn();
  draw();
  drawNextPiece();
  drawHoldPiece();
  updateUI();
  
  lastTime = performance.now();
  requestAnimationFrame(gameLoop);
}

function initGameState() {
  field = Array.from({length: ROWS}, () => Array(COLS).fill(""));
  score = 0;
  combo = -1;
  backToBack = false;
  totalLinesCleared = 0;
  heldPiece = null;
  canHold = true;
  gameOver = false;
  gameEndHandled = false;
  isPaused = false;
  lockDelay = 0;
  moveResets = 0;
  bag = [];
  dropCounter = 0;
  rotationState = 0;
  isSpectating = false;
  lastFieldUpdate = 0;
  nextPiece = getNextPiece();
  updateUI();
}

function updateUI() {
  const scoreVal = document.getElementById('scoreValue');
  const unVal = document.getElementById('usernameValue');
  
  if (scoreVal) scoreVal.textContent = (score || 0).toLocaleString();
  if (unVal) unVal.textContent = username || 'Player';
}

function gameLoop(time) {
  if (gameOver) return;
  if (isPaused) { requestAnimationFrame(gameLoop); return; }
  
  const deltaTime = time - lastTime;
  lastTime = time;
  
  dropCounter += deltaTime;
  if (dropCounter > 1000) {
    drop();
    dropCounter = 0;
  }
  
  if (current && checkCollision(current.x, current.y + 1, current.shape)) {
    lockDelay += deltaTime;
    if (lockDelay >= lockDelayLimit || moveResets >= maxMoveResets) {
      merge();
      clearLines();
      spawn();
      lockDelay = 0;
      moveResets = 0;
      
      if (isOnline && ws && ws.readyState === WebSocket.OPEN) {
        sendFieldUpdate();
        lastFieldUpdate = time;
      }
    }
  } else {
    lockDelay = 0;
  }
  
  // 定期的にフィールド更新を送信（500msごと）
  if (isOnline && ws && ws.readyState === WebSocket.OPEN && time - lastFieldUpdate > fieldUpdateInterval) {
    sendFieldUpdate();
    lastFieldUpdate = time;
  }
  
  requestAnimationFrame(gameLoop);
}

function sendFieldUpdate() {
  try {
    ws.send(JSON.stringify({
      type: 'gameUpdate',
      score: score,
      linesCleared: totalLinesCleared,
      field: field,
      currentPiece: current ? {
        shape: current.shape,
        x: current.x,
        y: current.y,
        color: COLORS[current.type]
      } : null
    }));
  } catch(e) {}
}

// ========== 描画 ==========
function draw() {
  if (!ctx) return;
  
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  drawGrid();
  
  for (let y = 0; y < ROWS; y++) {
    for (let x = 0; x < COLS; x++) {
      if (field[y][x]) drawBlock(x, y, field[y][x]);
    }
  }
  
  if (current) {
    drawGhost();
    for (let y = 0; y < current.shape.length; y++) {
      for (let x = 0; x < current.shape[y].length; x++) {
        if (current.shape[y][x]) {
          drawBlock(current.x + x, current.y + y, COLORS[current.type]);
        }
      }
    }
  }
  
  updateUI();
}

function drawGrid() {
  if (!ctx) return;
  ctx.strokeStyle = "#ffffff22";
  ctx.lineWidth = 1;
  for (let x = 0; x <= COLS; x++) {
    ctx.beginPath();
    ctx.moveTo(x * BLOCK_SIZE, 0);
    ctx.lineTo(x * BLOCK_SIZE, ROWS * BLOCK_SIZE);
    ctx.stroke();
  }
  for (let y = 0; y <= ROWS; y++) {
    ctx.beginPath();
    ctx.moveTo(0, y * BLOCK_SIZE);
    ctx.lineTo(COLS * BLOCK_SIZE, y * BLOCK_SIZE);
    ctx.stroke();
  }
}

function drawBlock(x, y, color) {
  if (!ctx) return;
  const grad = ctx.createLinearGradient(
    x * BLOCK_SIZE, y * BLOCK_SIZE,
    (x + 1) * BLOCK_SIZE, (y + 1) * BLOCK_SIZE
  );
  grad.addColorStop(0, "#fff");
  grad.addColorStop(0.3, color);
  grad.addColorStop(1, "#000");
  ctx.fillStyle = grad;
  ctx.fillRect(x * BLOCK_SIZE, y * BLOCK_SIZE, BLOCK_SIZE, BLOCK_SIZE);
  ctx.strokeStyle = "#fff";
  ctx.strokeRect(x * BLOCK_SIZE, y * BLOCK_SIZE, BLOCK_SIZE, BLOCK_SIZE);
}

function drawGhost() {
  if (!current || !ctx) return;
  let ghostY = current.y;
  while (!checkCollision(current.x, ghostY + 1, current.shape)) {
    ghostY++;
  }
  ctx.globalAlpha = 0.3;
  for (let y = 0; y < current.shape.length; y++) {
    for (let x = 0; x < current.shape[y].length; x++) {
      if (current.shape[y][x]) {
        drawBlock(current.x + x, ghostY + y, COLORS[current.type]);
      }
    }
  }
  ctx.globalAlpha = 1.0;
}

function drawNextPiece() {
  if (!nextCtx || !nextPiece) return;
  nextCtx.clearRect(0, 0, nextCanvas.width, nextCanvas.height);
  const shape = SHAPES[nextPiece];
  const color = COLORS[nextPiece];
  const size = Math.floor(Math.min(nextCanvas.width / (shape[0].length + 1), nextCanvas.height / (shape.length + 1)));
  const offsetX = (nextCanvas.width - shape[0].length * size) / 2;
  const offsetY = (nextCanvas.height - shape.length * size) / 2;
  
  for (let y = 0; y < shape.length; y++) {
    for (let x = 0; x < shape[y].length; x++) {
      if (shape[y][x]) {
        drawPreviewBlock(nextCtx, offsetX / size + x, offsetY / size + y, color, size);
      }
    }
  }
}

function drawHoldPiece() {
  if (!holdCtx) return;
  holdCtx.clearRect(0, 0, holdCanvas.width, holdCanvas.height);
  if (!heldPiece) return;
  
  const shape = SHAPES[heldPiece];
  const color = COLORS[heldPiece];
  const size = Math.floor(Math.min(holdCanvas.width / (shape[0].length + 1), holdCanvas.height / (shape.length + 1)));
  const offsetX = (holdCanvas.width - shape[0].length * size) / 2;
  const offsetY = (holdCanvas.height - shape.length * size) / 2;
  
  for (let y = 0; y < shape.length; y++) {
    for (let x = 0; x < shape[y].length; x++) {
      if (shape[y][x]) {
        drawPreviewBlock(holdCtx, offsetX / size + x, offsetY / size + y, color, size);
      }
    }
  }
}

function drawPreviewBlock(context, x, y, color, size) {
  const grad = context.createLinearGradient(
    x * size, y * size,
    (x + 1) * size, (y + 1) * size
  );
  grad.addColorStop(0, "#fff");
  grad.addColorStop(0.3, color);
  grad.addColorStop(1, "#000");
  context.fillStyle = grad;
  context.fillRect(x * size, y * size, size, size);
  context.strokeStyle = "#fff";
  context.strokeRect(x * size, y * size, size, size);
}

// ========== 操作 ==========
function spawn() {
  current = {
    type: nextPiece,
    shape: JSON.parse(JSON.stringify(SHAPES[nextPiece])),
    x: 3,
    y: 0
  };
  
  nextPiece = getNextPiece();
  drawNextPiece();
  rotationState = 0;
  canHold = true;
  
  if (checkCollision(current.x, current.y, current.shape)) {
    endGame();
  }
}

function rotate(clockwise = true) {
  if (!current) return;
  
  const oldRot = rotationState;
  let newRot;
  
  if (clockwise) {
    newRot = oldRot === 0 ? 'R' : (oldRot === 'R' ? 2 : (oldRot === 2 ? 'L' : 0));
  } else {
    newRot = oldRot === 0 ? 'L' : (oldRot === 'L' ? 2 : (oldRot === 2 ? 'R' : 0));
  }
  
  let rotated = current.shape[0].map((_, i) =>
    current.shape.map(row => row[i]).reverse()
  );
  
  if (!clockwise) {
    for (let i = 0; i < 2; i++) {
      rotated = rotated[0].map((_, i) =>
        rotated.map(row => row[i]).reverse()
      );
    }
  }
  
  const kickKey = current.type === 'I' ? 'I' : 'JLSTZ';
  const kicks = WALL_KICKS[kickKey][`${oldRot}->${newRot}`] || [[0,0]];
  
  for (let [dx, dy] of kicks) {
    if (!checkCollision(current.x + dx, current.y - dy, rotated)) {
      current.shape = rotated;
      current.x += dx;
      current.y -= dy;
      rotationState = newRot;
      
      if (checkCollision(current.x, current.y + 1, current.shape)) {
        if (moveResets < maxMoveResets) {
          lockDelay = 0;
          moveResets++;
        }
      }
      
      draw();
      return;
    }
  }
}

function move(dir) {
  if (!current) return;
  if (!checkCollision(current.x + dir, current.y, current.shape)) {
    current.x += dir;
    
    if (checkCollision(current.x, current.y + 1, current.shape)) {
      if (moveResets < maxMoveResets) {
        lockDelay = 0;
        moveResets++;
      }
    }
    
    draw();
  }
}

function drop() {
  if (!current) return;
  if (!checkCollision(current.x, current.y + 1, current.shape)) {
    current.y++;
    draw();
  }
}

function softDrop() {
  if (!current) return;
  if (!checkCollision(current.x, current.y + 1, current.shape)) {
    current.y++;
    score += 1;
    draw();
  }
}

function hardDrop() {
  if (!current) return;
  let dist = 0;
  while (!checkCollision(current.x, current.y + 1, current.shape)) {
    current.y++;
    dist++;
  }
  score += dist * 2;
  merge();
  clearLines();
  spawn();
  draw();
  
  if (isOnline && ws && ws.readyState === WebSocket.OPEN) {
    sendFieldUpdate();
  }
}

function holdPiece() {
  if (!canHold || !current) return;
  
  if (heldPiece === null) {
    heldPiece = current.type;
    spawn();
  } else {
    const temp = heldPiece;
    heldPiece = current.type;
    current = {
      type: temp,
      shape: JSON.parse(JSON.stringify(SHAPES[temp])),
      x: 3,
      y: 0
    };
    rotationState = 0;
    
    if (checkCollision(current.x, current.y, current.shape)) {
      endGame();
      return;
    }
  }
  
  canHold = false;
  drawHoldPiece();
  draw();
}

function checkCollision(x, y, shape) {
  for (let row = 0; row < shape.length; row++) {
    for (let col = 0; col < shape[row].length; col++) {
      if (shape[row][col]) {
        const nx = x + col;
        const ny = y + row;
        if (nx < 0 || nx >= COLS || ny >= ROWS || (ny >= 0 && field[ny][nx])) {
          return true;
        }
      }
    }
  }
  return false;
}

// ========== ライン消去 ==========
function merge() {
  for (let y = 0; y < current.shape.length; y++) {
    for (let x = 0; x < current.shape[y].length; x++) {
      if (current.shape[y][x]) {
        if (current.y + y >= 0) {
          field[current.y + y][current.x + x] = COLORS[current.type];
        }
      }
    }
  }
}

function clearLines() {
  let cleared = 0;
  const isTSpin = checkTSpin();
  
  for (let y = ROWS - 1; y >= 0; y--) {
    if (field[y].every(cell => cell)) {
      field.splice(y, 1);
      field.unshift(Array(COLS).fill(""));
      cleared++;
      y++;
    }
  }
  
  if (cleared > 0) {
    totalLinesCleared += cleared;
    
    let points = 0;
    const isDifficult = cleared === 4 || (isTSpin && cleared > 0);
    
    if (isTSpin) {
      points = [0, 800, 1200, 1600][cleared] || 0;
    } else {
      points = [0, 100, 300, 500, 800][cleared] || 0;
    }
    
    if (isDifficult) {
      if (backToBack) points = Math.floor(points * 1.5);
      backToBack = true;
      showIndicator('btbIndicator', 'BACK-TO-BACK!');
    } else {
      backToBack = false;
    }
    
    combo++;
    if (combo > 0) {
      points += 50 * combo;
      showIndicator('comboIndicator', `COMBO x${combo}`);
    }
    
    score += points;
    if (score > highscore) {
      highscore = score;
      saveSettings();
    }
    
    if (isOnline && ws && ws.readyState === WebSocket.OPEN) {
      sendAttack(cleared, isTSpin);
    }
    if (gameMode === 'cpu1v1') {
      sendAttack(cleared, isTSpin);
    }
  } else {
    combo = -1;
  }
}

function sendAttack(cleared, isTSpin) {
  let attackLines = 0;
  
  if (isTSpin) {
    attackLines = cleared * 2;
  } else if (cleared === 4) {
    attackLines = 4;
  } else if (cleared >= 2) {
    attackLines = cleared - 1;
  }
  
  // コンボボーナス（コンボ数に応じて攻撃力上昇）
  const comboBonus = combo > 0 ? Math.floor(combo * 0.5) : 0;
  attackLines += comboBonus;
  
  if (attackLines <= 0) return;
  
  // CPU1v1の場合はCPUに攻撃
  if (gameMode === 'cpu1v1' && cpuOpponent && cpuOpponent.isAlive) {
    cpuOpponent.receiveGarbage(attackLines);
    showIndicator('attackIndicator', `⚔️ ATTACK ${attackLines}L`);
    return;
  }
  
  // オンラインの場合はサーバーへ
  if (isOnline && ws && ws.readyState === WebSocket.OPEN) {
    try {
      ws.send(JSON.stringify({ type: 'attack', targetId: 'random', lines: attackLines }));
    } catch(e) {}
  }
}

function checkTSpin() {
  if (!current || current.type !== 'T') return false;
  
  const corners = [
    [current.x, current.y],
    [current.x + 2, current.y],
    [current.x, current.y + 2],
    [current.x + 2, current.y + 2]
  ];
  
  let filled = 0;
  for (let [x, y] of corners) {
    if (x < 0 || x >= COLS || y < 0 || y >= ROWS || (field[y] && field[y][x])) {
      filled++;
    }
  }
  
  return filled >= 3;
}

function showIndicator(id, text) {
  const ind = document.getElementById(id);
  if (!ind) return;
  ind.textContent = text;
  ind.style.display = 'block';
  setTimeout(() => {
    ind.style.display = 'none';
  }, 2000);
}

// ========== ゲーム終了 ==========
function endGame(forced = false) {
  console.log('Game over, forced:', forced);
  
  const gameScreen = document.getElementById('gameScreen');
  if (!gameScreen || !gameScreen.classList.contains('active')) return;
  if (gameOver && !forced) return;
  
  gameOver = true;
  current = null;
  
  // オンライン系：死亡通知 & 観戦へ
  if (isOnline && ws && ws.readyState === WebSocket.OPEN && !forced) {
    try { ws.send(JSON.stringify({ type: 'gameOver', score })); } catch(e) {}
    const alivePlayers = Array.from(onlinePlayers.values()).filter(p => !p.isDead);
    if (alivePlayers.length > 0) {
      enterSpectateMode();
      return;
    }
  }
  
  // CPU 1v1：勝敗判定
  if (gameMode === 'cpu1v1') {
    const cpuDead = cpuOpponent && !cpuOpponent.isAlive;
    const position = cpuDead ? 1 : 2; // CPUが先に死んでいれば勝ち
    const ratingResult = updateRating(position, 2);
    showGameOverModal(ratingResult);
    return;
  }
  
  // シングル：スコアでレート更新
  if (gameMode === 'single') {
    const ratingResult = updateRating(1, 1); // position=1 でスコア基準計算
    updateTitleStats();
    showGameOverModal(ratingResult);
    return;
  }
  
  showGameOverModal(null);
}

function showGameOverModal(ratingResult) {
  const finalScore = document.getElementById('finalScoreText');
  if (finalScore) {
    if (score === highscore && score > 0) {
      finalScore.innerHTML = `SCORE: ${score.toLocaleString()}<br><span class="new-record">🎉 NEW RECORD! 🎉</span>`;
    } else {
      finalScore.innerHTML = `SCORE: ${score.toLocaleString()}<br>HIGH SCORE: ${highscore.toLocaleString()}`;
    }
  }
  
  const ratingChangeText = document.getElementById('ratingChangeText');
  if (ratingChangeText) {
    if (ratingResult && ratingResult.change !== 0) {
      const sign = ratingResult.change > 0 ? '+' : '';
      ratingChangeText.innerHTML = `レート: ${ratingResult.oldRating} → ${rating} (${sign}${ratingResult.change})<br>ランク: ${ratingResult.newRank}`;
    } else {
      ratingChangeText.innerHTML = '';
    }
  }
  
  document.getElementById('gameOverModal')?.classList.add('active');
}

function restartGame() {
  document.getElementById('gameOverModal')?.classList.remove('active');
  if (cpuIntervalId) { clearInterval(cpuIntervalId); cpuIntervalId = null; }
  cpuOpponent = null;
  if (gameMode === 'single') {
    startSinglePlayer();
  } else if (gameMode === 'cpu1v1') {
    startCPU1v1();
  } else if (isOnline) {
    leaveRoom();
  } else {
    showScreen('menuScreen');
  }
}

// ========== キーボード ==========
window.addEventListener("keydown", (e) => {
  // ポーズ（シングル・CPU1v1のみ）
  if (e.key === 'Escape' || e.key === 'p' || e.key === 'P') {
    if (gameMode === 'single' || gameMode === 'cpu1v1') {
      e.preventDefault();
      togglePause();
      return;
    }
  }
  
  if (gameOver || !current || isSpectating || isPaused) return;
  
  const key = e.key;
  
  if (key === keys.left) { e.preventDefault(); move(-1); }
  else if (key === keys.right) { e.preventDefault(); move(1); }
  else if (key === keys.softDrop) { e.preventDefault(); softDrop(); }
  else if (key === keys.rotateL) { e.preventDefault(); rotate(false); }
  else if (key === keys.rotateR || key === 'ArrowUp') { e.preventDefault(); rotate(true); }
  else if (key === keys.hardDrop) { e.preventDefault(); hardDrop(); }
  else if (key === keys.hold) { e.preventDefault(); holdPiece(); }
});

function togglePause() {
  if (gameOver) return;
  isPaused = !isPaused;
  const pauseOverlay = document.getElementById('pauseOverlay');
  if (pauseOverlay) pauseOverlay.style.display = isPaused ? 'flex' : 'none';
  if (!isPaused) {
    lastTime = performance.now();
    requestAnimationFrame(gameLoop);
  }
}

function abortGame() {
  // ポーズオーバーレイを閉じる
  const pauseOverlay = document.getElementById('pauseOverlay');
  if (pauseOverlay) pauseOverlay.style.display = 'none';
  isPaused = false;
  
  // CPU停止
  if (cpuIntervalId) { clearInterval(cpuIntervalId); cpuIntervalId = null; }
  
  // レート計算（中断=負け扱い）
  const ratingResult = updateRating(gameMode === 'cpu1v1' ? 2 : 1, gameMode === 'cpu1v1' ? 2 : 1);
  updateTitleStats();
  
  // ゲームオーバー扱い
  gameOver = true;
  current = null;
  showGameOverModal(ratingResult);
}

// ========== タッチ ==========
function setupTouchControls() {
  let longPressTimer = null;
  let longPressActive = false;
  
  const setup = (id, fn) => {
    const btn = document.getElementById(id);
    if (!btn) return;
    btn.addEventListener('click', fn);
    btn.addEventListener('touchstart', (e) => { e.preventDefault(); fn(); }, { passive: false });
  };
  
  // 左右ボタンは長押し対応（端まで移動）
  const setupLR = (id, dir) => {
    const btn = document.getElementById(id);
    if (!btn) return;
    
    const guard = () => !gameOver && current && !isSpectating && !isPaused;
    
    const start = (e) => {
      if (e.cancelable) e.preventDefault();
      if (!guard()) return;
      move(dir);
      longPressActive = false;
      longPressTimer = setTimeout(() => {
        longPressActive = true;
        // 一番端まで移動
        if (guard()) {
          while (!checkCollision(current.x + dir, current.y, current.shape)) {
            current.x += dir;
          }
          draw();
        }
      }, 400);
    };
    
    const end = () => {
      if (longPressTimer) { clearTimeout(longPressTimer); longPressTimer = null; }
    };
    
    btn.addEventListener('touchstart', start, { passive: false });
    btn.addEventListener('touchend', end);
    btn.addEventListener('touchcancel', end);
    btn.addEventListener('mousedown', start);
    btn.addEventListener('mouseup', end);
    btn.addEventListener('click', () => { if (!longPressActive && guard()) move(dir); });
  };
  
  setupLR('btnLeft', -1);
  setupLR('btnRight', 1);
  
  setup('btnDown', () => { if (!gameOver && current && !isSpectating && !isPaused) softDrop(); });
  setup('btnRotateL', () => { if (!gameOver && current && !isSpectating && !isPaused) rotate(false); });
  setup('btnRotateR', () => { if (!gameOver && current && !isSpectating && !isPaused) rotate(true); });
  setup('btnDrop', () => { if (!gameOver && current && !isSpectating && !isPaused) hardDrop(); });
  setup('btnHold', () => { if (!gameOver && current && !isSpectating && !isPaused) holdPiece(); });
}