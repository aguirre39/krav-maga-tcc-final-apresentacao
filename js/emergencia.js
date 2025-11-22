// ===================================================================================
// MÓDULO DE EMERGÊNCIA (emergencia.js)
// Gerencia o acompanhamento de trajeto, contatos de confiança e alertas.
// ===================================================================================

// Importa funções do Firebase Realtime Database
import { getDatabase, ref, set, get, push, remove, onValue, off, update, query, orderByChild, equalTo } from "https://www.gstatic.com/firebasejs/11.6.1/firebase-database.js";

// Variáveis de estado do módulo
let db, showMessage, showLoader, hideLoader;
let currentUserId;
let emergencyLinkModalInstance, safetyCheckResponseModalInstance, userSafetyCheckModalInstance, emergencyActionModalInstance;
let locationWatchId = null;
let currentEmergencySessionId = null;
let checkRequestListener = null;
let modoAlertaAtivo = false; 

// --- VARIÁVEIS DE CONTROLE E PATCHES ---
let lastFirebaseUpdateTimestamp = 0; 
let contactsListener = null; 
let lastLocation = null; 
let monitoringStartTime = 0; // Variável para controlar o tempo de aquecimento do GPS

// --- CONFIGURAÇÃO DE DETECÇÃO DE ANOMALIA (AJUSTADO PARA SALA DE AULA) ---
// 15 m/s (~54 km/h) = Carro (Padrão Real)
// 4.5 m/s (~16 km/h) = Corrida vigorosa / Drift de GPS indoor
// AVISO: Se disparar sozinho, aumente para 6.0. Se não disparar correndo, diminua para 3.0.
const ANOMALY_THRESHOLD_MPS = 6.0; 

// Constantes para o ciclo de verificação de segurança
const USER_CHECK_VISIBILITY_DURATION_MS = 15000; 
const USER_CHECK_INTERVAL_MS = 15000; 
let userSafetyCheckIntervalId = null; 
let userSafetyCheckVisibilityTimeoutId = null; 

// Mapeamento dos elementos da UI
const ui = {
    emergencyButton: document.getElementById('emergencyButton'),
    emergencyStatus: document.getElementById('emergencyStatus'),
    checkContactButton: document.getElementById('checkContactButton'),
    trackingLinkInput: document.getElementById('trackingLinkInput'),
    copyLinkButton: document.getElementById('copyLinkButton'),
    shareButton: document.getElementById('shareButton'),
    copyStatus: document.getElementById('copyStatus'),
    safetyCheckResponseModalIcon: document.getElementById('safetyCheckResponseModalIcon'),
    safetyCheckResponseModalText: document.getElementById('safetyCheckResponseModalText'),
    safetyCheckResponseModalHeader: document.getElementById('safetyCheckResponseModalHeader'),
    contactNameInput: document.getElementById('contactName'),
    contactDetailInput: document.getElementById('contactDetail'),
    addContactButton: document.getElementById('addContactButton'),
    contactsListDiv: document.getElementById('contactsList'),
    userSafetyCheckYes: document.getElementById('userSafetyCheckYes'),
    userSafetyCheckNo: document.getElementById('userSafetyCheckNo'),
    warnContactsButton: document.getElementById('warnContactsButton'),
    cancelEmergencyButton: document.getElementById('cancelEmergencyButton')
};

// --- Funções de Validação e Formatação ---

function isValidEmail(email) {
    const re = /^(([^<>()[\]\\.,;:\s@"]+(\.[^<>()[\]\\.,;:\s@"]+)*)|(".+"))@((\[[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}])|(([a-zA-Z\-0-9]+\.)+[a-zA-Z]{2,}))$/;
    return re.test(String(email).toLowerCase());
}

function isValidPhone(phone) {
    const cleaned = phone.replace(/\D/g, '');
    return cleaned.length === 10 || cleaned.length === 11;
}

function isValidTelegramUsername(detail) {
    return typeof detail === 'string' && detail.startsWith('@') && detail.length > 1;
}

function maskPhone(value) {
    value = value.replace(/\D/g, '');
    value = value.replace(/^(\d{2})(\d)/g, '($1) $2');
    value = value.replace(/(\d)(\d{4})$/, '$1-$2');
    return value;
}

// --- Inicialização do Módulo ---

export function setupEmergencia(dependencies) {
    if (dependencies) {
        db = dependencies.db;
        showMessage = dependencies.showMessage;
        showLoader = dependencies.showLoader;
        hideLoader = dependencies.hideLoader;
        emergencyLinkModalInstance = dependencies.emergencyLinkModalInstance;
        safetyCheckResponseModalInstance = dependencies.safetyCheckResponseModalInstance;
        userSafetyCheckModalInstance = dependencies.userSafetyCheckModalInstance;
        emergencyActionModalInstance = dependencies.emergencyActionModalInstance;
    } else {
        console.error("Módulo de Emergência: Dependências não fornecidas!");
        return {};
    }

    if (ui.emergencyButton) ui.emergencyButton.addEventListener('click', toggleEmergencyAlert);
    if (ui.checkContactButton) ui.checkContactButton.addEventListener('click', handleCheckContact);
    if (ui.copyLinkButton) ui.copyLinkButton.addEventListener('click', handleCopyLink);
    if (ui.shareButton) ui.shareButton.addEventListener('click', handleShare);
    if (ui.addContactButton) ui.addContactButton.addEventListener('click', handleAddEmergencyContact);

    if (ui.contactDetailInput) {
        ui.contactDetailInput.placeholder = "Telefone (ex: (11) 9...) ou Telegram (@usuario)";
        ui.contactDetailInput.addEventListener('input', (e) => {
            const value = e.target.value;
            if (!value.includes('@')) {
                e.target.value = maskPhone(value);
            }
        });
    }

    if (ui.userSafetyCheckYes) ui.userSafetyCheckYes.addEventListener('click', handleUserSafetyCheckYes);
    if (ui.userSafetyCheckNo) ui.userSafetyCheckNo.addEventListener('click', handleUserSafetyCheckNo);
    if (ui.cancelEmergencyButton) ui.cancelEmergencyButton.addEventListener('click', handleCancelPanicMode);
    
    window.addEventListener('beforeunload', () => {
        if (currentEmergencySessionId) {
            update(ref(db, `emergencySessions/${currentEmergencySessionId}`), {
                status: 'connection_lost',
                lastEventTimestamp: new Date().toISOString()
            });
        }
    });

    // --- EXPOR FUNÇÃO DE TESTE NO CONSOLE ---
    // Para usar: Abra o console (F12) e digite: debugSimularAnomalia()
    window.debugSimularAnomalia = async () => {
        if (!currentEmergencySessionId || !lastLocation) {
            console.error("Erro: Inicie o acompanhamento primeiro.");
            alert("Inicie o acompanhamento antes de simular.");
            return;
        }
        console.warn("🛠️ SIMULANDO MOVIMENTO BRUSCO (ANOMALIA)...");
        
        // Cria uma coordenada falsa longe da atual para gerar alta velocidade matemática
        const fakeLocation = {
            ...lastLocation,
            latitude: lastLocation.latitude + 0.005, // ~500m de salto
            longitude: lastLocation.longitude + 0.005,
            timestamp: new Date().toISOString(),
            speed: 100 // m/s simulados
        };
        
        // Força a detecção (ignora o warm-up na simulação manual)
        detectAnomalies(fakeLocation, true);
        
        // Atualiza no Firebase para o Tracker ver
        await update(ref(db, `emergencySessions/${currentEmergencySessionId}`), {
            anomalyDetected: true,
            lastEventTimestamp: new Date().toISOString()
        });
        alert("Simulação enviada! Verifique a tela do Tracker.");
    };

    return {
        loadEmergencyContacts,
        resumeActiveSession 
    };
}

// ===================================================================================
// SEÇÃO 1: CORREÇÃO DE CONSISTÊNCIA DA SESSÃO (RESUME)
// ===================================================================================

export async function resumeActiveSession(userId) {
    if (!userId) return;
    currentUserId = userId; 

    console.log("Verificando sessões ativas para o usuário:", userId);

    try {
        const sessionsRef = ref(db, 'emergencySessions');
        const q = query(
            sessionsRef,
            orderByChild('userId'),
            equalTo(userId)
        );

        const snapshot = await get(q);

        if (snapshot.exists()) {
            let sessionToResume = null;
            let sessionId = null;

            snapshot.forEach(childSnapshot => {
                const session = childSnapshot.val();
                if (session.status === "active" || session.status === "connection_lost") {
                    sessionToResume = session;
                    sessionId = childSnapshot.key;
                }
            });

            if (sessionToResume && sessionId) {
                console.warn(`Resumindo sessão ativa encontrada: ${sessionId}`);

                currentEmergencySessionId = sessionId;
                modoAlertaAtivo = (sessionToResume.status === 'panic_triggered_by_user'); 
                lastLocation = sessionToResume.liveLocation || sessionToResume.initialLocation;
                monitoringStartTime = Date.now(); // Reinicia o warm-up ao resumir

                ui.emergencyButton.innerHTML = '<i class="fas fa-times-circle me-2"></i>ENCERRAR ACOMPANHAMENTO';
                ui.emergencyButton.classList.remove('btn-danger', 'emergency-button-pulse-animation');
                ui.emergencyButton.classList.add('btn-danger-active');
                ui.checkContactButton.style.display = 'block';
                ui.emergencyStatus.textContent = "Acompanhamento (resumido) ativo.";
                ui.emergencyStatus.classList.remove('d-none');

                const checkRequestRef = ref(db, `emergencySessions/${currentEmergencySessionId}/checkRequest`);
                if (checkRequestListener) off(checkRequestRef, 'value', checkRequestListener);
                checkRequestListener = onValue(checkRequestRef, handleCheckRequestUpdate);

                if (locationWatchId) navigator.geolocation.clearWatch(locationWatchId);

                lastFirebaseUpdateTimestamp = Date.now(); 
                locationWatchId = navigator.geolocation.watchPosition(
                    handleLocationUpdate, 
                    handleLocationError,
                    { enableHighAccuracy: true, timeout: 20000, maximumAge: 0 }
                );

                if (!modoAlertaAtivo) {
                    startUserSafetyCheckCycle();
                }

                if (sessionToResume.status === "connection_lost") {
                     await update(ref(db, `emergencySessions/${currentEmergencySessionId}`), {
                        status: 'active',
                        lastEventTimestamp: new Date().toISOString()
                    });
                }
            }
        }
    } catch (error) {
        console.error("Erro ao tentar resumir sessão:", error);
        showMessage("Erro ao verificar sessões anteriores.", true);
    }
}


// --- Lógica de Acompanhamento de Trajeto ---

function toggleEmergencyAlert() {
    locationWatchId ? handleCancelEmergencyAlert() : handleActivateEmergencyAlert();
}

// ===================================================================================
// 🔐 SEGURANÇA AVANÇADA — FAIL-SAFE, MODO SILENCIOSO E DETECÇÃO ANÔMALA
// ===================================================================================

// --- DETECÇÃO DE MOVIMENTO ANÔMALO ---
function detectAnomalies(newLocation, forceTest = false) {
    if (!lastLocation) { lastLocation = newLocation; return; }

    // PROTEÇÃO DE ESTABILIZAÇÃO (WARM-UP):
    // Ignora anomalias nos primeiros 10 segundos para evitar o "pulo" inicial do GPS.
    if (!forceTest && (Date.now() - monitoringStartTime < 10000)) {
        console.log("Estabilizando GPS... Anomalias ignoradas.");
        lastLocation = newLocation;
        return;
    }

    if (lastLocation.timestamp) {
        const R = 6371e3; 
        const φ1 = lastLocation.latitude * Math.PI / 180;
        const φ2 = newLocation.latitude * Math.PI / 180;
        const Δλ = (newLocation.longitude - lastLocation.longitude) * Math.PI / 180;
        const d = Math.acos(Math.sin(φ1) * Math.sin(φ2) +
                            Math.cos(φ1) * Math.cos(φ2) * Math.cos(Δλ)) * R;

        const timeDiff = (new Date(newLocation.timestamp) - new Date(lastLocation.timestamp)) / 1000;

        if (timeDiff > 0) { 
            const speed = d / timeDiff; // m/s

            // Utiliza a constante calibrada (4.5 m/s)
            if (speed > ANOMALY_THRESHOLD_MPS) { 
                console.warn(`⚠️ Movimento anômalo detectado: ${speed.toFixed(2)} m/s (Limite: ${ANOMALY_THRESHOLD_MPS} m/s)`);
                update(ref(db, `emergencySessions/${currentEmergencySessionId}`), {
                    anomalyDetected: true,
                    speedDetected: speed,
                    lastEventTimestamp: new Date().toISOString()
                });
            }
        }
    }

    lastLocation = newLocation;
}

// --- MODO DE PÂNICO SILENCIOSO ---
async function handleSilentPanic() {
    modoAlertaAtivo = true;

    if (currentEmergencySessionId) {
        await update(ref(db, `emergencySessions/${currentEmergencySessionId}`), {
            status: 'panic_triggered_by_user',
            silentMode: true, 
            lastEventTimestamp: new Date().toISOString()
        });
        console.log("🚨 Alerta silencioso enviado — tela permanece normal.");
    }
}

// ===================================================================================
// SEÇÃO 2: OTIMIZAÇÃO DE RASTREAMENTO (THROTTLING)
// ===================================================================================

function getHaversineDistance(coords1, coords2) {
    const R = 6371e3; 
    const φ1 = coords1.latitude * Math.PI / 180;
    const φ2 = coords2.latitude * Math.PI / 180;
    const Δφ = (coords2.latitude - coords1.latitude) * Math.PI / 180;
    const Δλ = (coords2.longitude - coords1.longitude) * Math.PI / 180;

    const a = Math.sin(Δφ / 2) * Math.sin(Δφ / 2) +
              Math.cos(φ1) * Math.cos(φ2) *
              Math.sin(Δλ / 2) * Math.sin(Δλ / 2);
    const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));

    return R * c; 
}

function handleLocationUpdate(pos) {
    const now = Date.now();
    const MIN_UPDATE_INTERVAL_MS = 10000; // 10 segundos
    const MIN_UPDATE_DISTANCE_METERS = 20; // 20 metros

    const { latitude, longitude, accuracy, heading, speed } = pos.coords;
    const liveLocationData = {
        latitude, longitude, accuracy,
        heading: heading ?? null,
        speed: speed ?? null,
        timestamp: new Date().toISOString()
    };

    const distanceMoved = lastLocation ? getHaversineDistance(lastLocation, liveLocationData) : 0;

    if ( (now - lastFirebaseUpdateTimestamp > MIN_UPDATE_INTERVAL_MS) ||
         (distanceMoved > MIN_UPDATE_DISTANCE_METERS) ) {

        console.log(`Atualizando Firebase: (Tempo: ${now - lastFirebaseUpdateTimestamp > MIN_UPDATE_INTERVAL_MS}, Dist: ${distanceMoved > MIN_UPDATE_DISTANCE_METERS})`);

        lastFirebaseUpdateTimestamp = now; 
        const sessionPath = `emergencySessions/${currentEmergencySessionId}`;

        set(ref(db, `${sessionPath}/liveLocation`), liveLocationData);
        push(ref(db, `${sessionPath}/path`), liveLocationData); 

        update(ref(db, sessionPath), { heartbeat: new Date().toISOString() });

        detectAnomalies(liveLocationData); 

    } else {
        // Verifica anomalia mesmo que o throttle bloqueie o envio, para segurança local
        detectAnomalies(liveLocationData);
    }
}

function handleLocationError(error) {
    ui.emergencyStatus.textContent = "Erro no rastreamento: " + error.message;
    console.error("Geolocation watchPosition Error:", error);
}


async function handleActivateEmergencyAlert() {
    if (!currentUserId) { showMessage("Você precisa estar logada para usar esta função.", true); return; }
    if (locationWatchId) return; 

    ui.emergencyButton.innerHTML = '<i class="fas fa-spinner fa-spin me-2"></i>INICIANDO...';
    ui.emergencyButton.disabled = true;

    try {
        const position = await new Promise((resolve, reject) => {
            navigator.geolocation.getCurrentPosition(resolve, reject, {
                enableHighAccuracy: true,
                timeout: 10000,
                maximumAge: 0
            });
        });
        const { latitude, longitude, accuracy } = position.coords;
        const locationData = { latitude, longitude, accuracy, timestamp: new Date().toISOString() };

        lastLocation = locationData; 
        monitoringStartTime = Date.now(); // Inicia contagem de estabilização

        const newSessionRef = push(ref(db, 'emergencySessions'));
        currentEmergencySessionId = newSessionRef.key;
        const sessionPath = `emergencySessions/${currentEmergencySessionId}`;

        await set(newSessionRef, {
            userId: currentUserId,
            status: "active",
            startTime: new Date().toISOString(),
            initialLocation: locationData,
            liveLocation: locationData, 
            heartbeat: new Date().toISOString() 
        });

        const trackingLink = `${window.location.origin}${window.location.pathname.replace('index.html', '')}tracker.html?session=${currentEmergencySessionId}`;
        ui.trackingLinkInput.value = trackingLink;
        emergencyLinkModalInstance.show();

        await notifyContactsViaCallMeBot(trackingLink);

        ui.emergencyButton.innerHTML = '<i class="fas fa-times-circle me-2"></i>ENCERRAR ACOMPANHAMENTO';
        ui.emergencyButton.classList.remove('btn-danger', 'emergency-button-pulse-animation');
        ui.emergencyButton.classList.add('btn-danger-active');
        ui.checkContactButton.style.display = 'block';
        ui.emergencyStatus.textContent = "Acompanhamento ativo. Compartilhe o link manualmente se necessário."; 
        ui.emergencyStatus.classList.remove('d-none');

        const checkRequestRef = ref(db, `${sessionPath}/checkRequest`);
        if (checkRequestListener) off(checkRequestRef, 'value', checkRequestListener);
        checkRequestListener = onValue(checkRequestRef, handleCheckRequestUpdate);

        lastFirebaseUpdateTimestamp = Date.now(); 
        locationWatchId = navigator.geolocation.watchPosition(
            handleLocationUpdate,
            handleLocationError,
            {
                enableHighAccuracy: true,
                timeout: 20000,
                maximumAge: 0
            }
        );

        modoAlertaAtivo = false; 
        startUserSafetyCheckCycle();

    } catch (error) {
        console.error("Erro ao ativar alerta de emergência:", error);
        showMessage("Não foi possível obter sua localização inicial: " + error.message, true);
        ui.emergencyButton.innerHTML = '<i class="fas fa-map-marker-alt me-2"></i> INICIAR ACOMPANHAMENTO';
        currentEmergencySessionId = null;
    } finally {
        ui.emergencyButton.disabled = false; 
    }
}

async function handleCancelEmergencyAlert() {
    if (!locationWatchId) return;

    navigator.geolocation.clearWatch(locationWatchId);
    locationWatchId = null;

    stopUserSafetyCheckCycle();
    modoAlertaAtivo = false;

    detachCheckRequestListener();

    showMessage("Acompanhamento de trajeto encerrado.");
    ui.emergencyStatus.textContent = "Acompanhamento encerrado.";

    if (currentUserId && currentEmergencySessionId) {
        const sessionPath = `emergencySessions/${currentEmergencySessionId}`;
        try {
            await update(ref(db, sessionPath), { 
                status: "cancelled",
                endTime: new Date().toISOString()
            });
        } catch (error) {
            console.error("Erro ao atualizar status da sessão para cancelado:", error);
        }
        currentEmergencySessionId = null;
    }

    ui.emergencyButton.innerHTML = '<i class="fas fa-map-marker-alt me-2"></i> INICIAR ACOMPANHAMENTO';
    ui.emergencyButton.classList.remove('btn-danger-active');
    ui.emergencyButton.classList.add('btn-danger', 'emergency-button-pulse-animation');
    ui.checkContactButton.style.display = 'none';
}

async function handleCheckContact() {
    if (!currentEmergencySessionId) {
        showMessage("Inicie o acompanhamento para poder verificar o contato.", true);
        return;
    }
    const checkRequestRef = ref(db, `emergencySessions/${currentEmergencySessionId}/checkRequest`);
    try {
        await set(checkRequestRef, {
            timestamp: new Date().toISOString(),
            status: 'pending'
        });
        showMessage("Verificação enviada ao seu contato. Aguardando resposta...");
    } catch (error) {
        console.error("Erro ao enviar solicitação de verificação:", error);
        showMessage("Erro ao enviar verificação para o contato.", true);
    }
}

function handleCheckRequestUpdate(snapshot) {
    const checkData = snapshot.val();

    if (checkData && checkData.status !== 'pending') {
        const { status } = checkData;

        ui.safetyCheckResponseModalIcon.classList.remove('fa-check-circle', 'fa-exclamation-triangle', 'text-success', 'text-danger');
        ui.safetyCheckResponseModalHeader.classList.remove('bg-danger', 'text-white');

        if (status === 'ok') {
            ui.safetyCheckResponseModalIcon.classList.add('fa-check-circle', 'text-success');
            ui.safetyCheckResponseModalText.textContent = "Seu contato confirmou que está tudo bem.";
        } else if (status === 'danger') {
            ui.safetyCheckResponseModalIcon.classList.add('fa-exclamation-triangle', 'text-danger');
            ui.safetyCheckResponseModalText.textContent = "ALERTA: Seu contato sinalizou que você pode estar em perigo. Considere ligar para a emergência (190) ou acionar o botão de pânico.";
            ui.safetyCheckResponseModalHeader.classList.add('bg-danger', 'text-white');
        }

        if (safetyCheckResponseModalInstance) safetyCheckResponseModalInstance.show();

        if (currentEmergencySessionId) {
            set(ref(db, `emergencySessions/${currentEmergencySessionId}/checkRequest`), null)
                .catch(error => console.error("Erro ao limpar checkRequest:", error));
        }
    }
}

function detachCheckRequestListener() {
    if (checkRequestListener && currentEmergencySessionId) {
        const checkRequestRef = ref(db, `emergencySessions/${currentEmergencySessionId}/checkRequest`);
        try {
            off(checkRequestRef, 'value', checkRequestListener);
        } catch (error) {
            console.error("Erro ao remover listener de checkRequest:", error);
        }
        checkRequestListener = null;
    }
}

// --- Lógica de Verificação de Segurança da Usuária ("Você está bem?") ---

function startUserSafetyCheckCycle() {
    if (modoAlertaAtivo) {
        console.log("Ciclo de verificação não iniciado: modo de alerta ativo.");
        return;
    }
    stopUserSafetyCheckCycle();
    showUserSafetyCheckModal();

    const totalCycleTime = USER_CHECK_VISIBILITY_DURATION_MS + USER_CHECK_INTERVAL_MS;
    userSafetyCheckIntervalId = setInterval(showUserSafetyCheckModal, totalCycleTime);
}

function stopUserSafetyCheckCycle() {
    if (userSafetyCheckIntervalId) {
        clearInterval(userSafetyCheckIntervalId);
        userSafetyCheckIntervalId = null;
    }
    if (userSafetyCheckVisibilityTimeoutId) {
        clearTimeout(userSafetyCheckVisibilityTimeoutId);
        userSafetyCheckVisibilityTimeoutId = null;
    }
    if (userSafetyCheckModalInstance) {
        try { userSafetyCheckModalInstance.hide(); } catch (e) { /* Ignora erro */ }
    }
}

function showUserSafetyCheckModal() {
    const isAnyModalOpen = document.body.classList.contains('modal-open');
    if (locationWatchId && !isAnyModalOpen && !modoAlertaAtivo) {
        userSafetyCheckModalInstance.show();

        if (userSafetyCheckVisibilityTimeoutId) clearTimeout(userSafetyCheckVisibilityTimeoutId);

        userSafetyCheckVisibilityTimeoutId = setTimeout(() => {
            const modalElement = document.getElementById('userSafetyCheckModal');
            if (modalElement && modalElement.classList.contains('show')) {
                userSafetyCheckModalInstance.hide();
            }
        }, USER_CHECK_VISIBILITY_DURATION_MS);
    } else if (modoAlertaAtivo) {
        console.log("Modal 'Você está bem?' não exibido: modo de alerta ativo.");
    }
}

async function handleUserSafetyCheckYes() {
    if (userSafetyCheckVisibilityTimeoutId) clearTimeout(userSafetyCheckVisibilityTimeoutId);
    userSafetyCheckModalInstance.hide();

    if (currentEmergencySessionId) {
        try {
            await update(ref(db, `emergencySessions/${currentEmergencySessionId}`), {
                userSafetyConfirmation: new Date().toISOString()
            });
            console.log("Confirmação de segurança ('Sim') enviada.");
        } catch (error) {
            console.error("Erro ao enviar confirmação de segurança ('Sim'):", error);
        }
    }
}

async function handleUserSafetyCheckNo() {
    console.log("Botão 'Não' clicado. Ativando modo de pânico DISCRETO.");

    modoAlertaAtivo = true;
    handleSilentPanic();
    stopUserSafetyCheckCycle();

    if (currentEmergencySessionId) {
         console.log("Status da sessão atualizado para panic_triggered_by_user (modo silencioso).");
    }
}

async function handleCancelPanicMode() {
    console.log("Cancelando modo de pânico.");
    modoAlertaAtivo = false;

    if (emergencyActionModalInstance) emergencyActionModalInstance.hide();

    if (currentEmergencySessionId) {
        try {
            await update(ref(db, `emergencySessions/${currentEmergencySessionId}`), {
                status: 'active',
                silentMode: false,
                lastEventTimestamp: new Date().toISOString()
            });
            showMessage("✅ Alerta cancelado. O acompanhamento continua ativo.", false);
            console.log("Status da sessão revertido para 'active'.");
            startUserSafetyCheckCycle();
        } catch (error) {
            showMessage("Erro ao cancelar o alerta no servidor.", true);
            console.error("Erro ao reverter status:", error);
        }
    } else {
        console.warn("Tentativa de cancelar pânico sem uma sessão ativa.");
    }
}

// --- Lógica de Compartilhamento do Link ---

function handleCopyLink() {
    if (!ui.trackingLinkInput) return;
    ui.trackingLinkInput.select();
    try {
        document.execCommand('copy');
        ui.copyStatus.textContent = "Link copiado!";
        setTimeout(() => { ui.copyStatus.textContent = ""; }, 3000);
    } catch (err) {
        showMessage('Não foi possível copiar o link automaticamente.', true);
    }
}

async function handleShare() {
    let link = ui.trackingLinkInput ? ui.trackingLinkInput.value : null;
    if (!link && currentEmergencySessionId) {
        link = `${window.location.origin}${window.location.pathname.replace('index.html', '')}tracker.html?session=${currentEmergencySessionId}`;
        if (ui.trackingLinkInput) ui.trackingLinkInput.value = link;
    } else if (!link) {
         showMessage("Inicie o acompanhamento para gerar um link para compartilhar.", true);
         return;
    }

    const shareData = {
        title: 'Acompanhe meu Trajeto - Krav Maga Woman',
        text: `ALERTA KMW: Estou iniciando meu acompanhamento de trajeto. Acompanhe minha localização em tempo real: ${link}`, // Mensagem padrão para compartilhamento
        url: link // A URL é redundante se já estiver no text, mas é bom ter
    };

    if (navigator.share) { // Verifica se a API Web Share está disponível
        try {
            await navigator.share(shareData);
            console.log('Link compartilhado com sucesso via Web Share API.');
            showMessage('Compartilhamento iniciado. Selecione seus contatos.');
        } catch (err) {
            // Ignora erro se o usuário cancelar o compartilhamento (AbortError)
            if (err.name !== 'AbortError') {
                console.error('Erro ao usar Web Share API:', err);
                 // Fallback para WhatsApp se Web Share falhar por outro motivo
                 openWhatsAppShare(shareData.text); // Passa apenas o texto formatado
            } else {
                 console.log('Compartilhamento cancelado pelo usuário.');
            }
        }
    } else {
        // Fallback para WhatsApp se Web Share não for suportado
        console.log('Web Share API não suportada. Usando fallback para WhatsApp.');
        openWhatsAppShare(shareData.text); // Passa apenas o texto formatado
    }
}

/** Abre o WhatsApp com uma mensagem pré-formatada contendo o link. */
function openWhatsAppShare(text) { // Recebe apenas o texto já formatado
    const whatsappUrl = `https://api.whatsapp.com/send?text=${encodeURIComponent(text)}`;
    // Tenta abrir em nova aba/janela. Pode ser bloqueado por pop-up blocker.
    const newWindow = window.open(whatsappUrl, '_blank');
    if (!newWindow || newWindow.closed || typeof newWindow.closed == 'undefined') {
         // Se falhou, informa o usuário para tentar copiar/colar manualmente
         showMessage('Não foi possível abrir o WhatsApp automaticamente. Copie o link e cole no app.', true);
    } else {
         showMessage('Abrindo WhatsApp para compartilhamento...');
    }
}

// ===================================================================================
// --- FUNCIONALIDADE: ENVIO VIA CALLMEBOT (MELHOR ESFORÇO - TELEGRAM) ---
// ===================================================================================

/**
 * @function sendCallMeBotTelegram
 * @description Tenta enviar uma mensagem via Telegram usando a API CallMeBot.
 * Requer que o destinatário (@username) tenha autorizado o bot @CallMeBot_txtbot.
 * @param {string} username - O username do Telegram do destinatário (sem o '@').
 * @param {string} message - A mensagem a ser enviada.
 * @returns {Promise<boolean>} - True se a API respondeu (não garante entrega), false se houve erro na requisição.
 */
async function sendCallMeBotTelegram(username, message) {
    const encodedMessage = encodeURIComponent(message);
    // Remove o '@' inicial do username para a URL da API
    const targetUser = username.startsWith('@') ? username.substring(1) : username;
    const apiUrl = `https://api.callmebot.com/text.php?user=${targetUser}&text=${encodedMessage}`;

    console.log(`Tentando enviar via CallMeBot Telegram para @${targetUser}...`);
    try {
        const response = await fetch(apiUrl); // GET request
        const responseText = await response.text(); // A API retorna texto simples

        // Verifica se a resposta indica sucesso (ou pelo menos que a API foi chamada)
        // A API CallMeBot geralmente retorna algo como "Message sent to @username" ou um erro.
        // Consideramos sucesso se a requisição foi feita, mesmo sem garantia de entrega ou autorização.
        if (response.ok && responseText.toLowerCase().includes("sent to")) {
            console.log(`SUCESSO (API CallMeBot Telegram): Resposta para @${targetUser}: ${responseText}`);
            return true;
        } else {
            console.error(`FALHA (API CallMeBot Telegram): Resposta inesperada para @${targetUser}: ${responseText} (Status: ${response.status})`);
            return false;
        }
    } catch (error) {
        console.error(`ERRO (REDE CallMeBot Telegram): Falha na requisição para @${targetUser}:`, error);
        return false;
    }
}

/**
 * @function sendCallMeBotWhatsapp
 * @description Tenta enviar uma mensagem via WhatsApp usando a API CallMeBot.
 * @param {string} phoneNumber - O número de telefone do destinatário no formato internacional (ex: +55119...).
 * @param {string} apiKey - A API Key do destinatário, obtida por ele no CallMeBot.
 * @param {string} message - A mensagem a ser enviada.
 * @returns {Promise<boolean>} - True se a API respondeu (não garante entrega), false se houve erro.
 */
async function sendCallMeBotWhatsapp(phoneNumber, apiKey, message) {
    const encodedMessage = encodeURIComponent(message);
    // Remove caracteres não numéricos do telefone para a URL
    const targetPhone = phoneNumber.replace(/\D/g, '');
    const apiUrl = `https://api.callmebot.com/whatsapp.php?phone=${targetPhone}&text=${encodedMessage}&apikey=${apiKey}`;

    console.log(`Tentando enviar via CallMeBot WhatsApp para ${targetPhone}...`);
    try {
        const response = await fetch(apiUrl);
        const responseText = await response.text();

        if (response.ok && !responseText.toLowerCase().includes("error")) {
            console.log(`SUCESSO (API CallMeBot WhatsApp): Resposta para ${targetPhone}: ${responseText}`);
            return true;
        } else {
            console.error(`FALHA (API CallMeBot WhatsApp): Resposta inesperada para ${targetPhone}: ${responseText} (Status: ${response.status})`);
            return false;
        }
    } catch (error) {
        console.error(`ERRO (REDE CallMeBot WhatsApp): Falha na requisição para ${targetPhone}:`, error);
        return false;
    }
}


/**
 * @function notifyContactsViaCallMeBot
 * @description Busca contatos de confiança e tenta notificar via Telegram e/ou WhatsApp.
 * @param {string} trackingLink - O link de acompanhamento gerado.
 */
async function notifyContactsViaCallMeBot(trackingLink) {
    if (!currentUserId) {
        console.error("ID do usuário não definido. Não é possível buscar contatos para CallMeBot.");
        return;
    }

    console.log("Iniciando processo de notificação via CallMeBot (Telegram e WhatsApp)...");
    const contactsRef = ref(db, `users/${currentUserId}/emergencyContacts`);

    try {
        const snapshot = await get(contactsRef);

        if (snapshot.exists()) {
            const notificationPromises = [];
            const msg = `ALERTA KMW: Estou iniciando meu acompanhamento. Localização: ${trackingLink}`;
            let validContactsFound = 0;

            snapshot.forEach(child => {
                const contact = child.val();
                console.log(`Processando contato para CallMeBot: ${contact.name} - ${contact.detail}`);

                // Verifica se o 'detail' é um username do Telegram válido
                if (contact && contact.detail && isValidTelegramUsername(contact.detail)) {
                    console.log(`Username válido do Telegram encontrado: ${contact.detail}`);
                    validContactsFound++;
                    notificationPromises.push(sendCallMeBotTelegram(contact.detail, msg));
                }
                // --- INÍCIO DA MODIFICAÇÃO: Bloco WhatsApp ativado ---
                else if (contact && contact.detail && isValidPhone(contact.detail.replace(/\D/g, ''))) {
                    const cleanedPhone = contact.detail.replace(/\D/g, ''); // Remove máscara e caracteres

                    // Verifica se o número é o seu, para o qual você tem a API Key
                    if (cleanedPhone === '51984672843') {
                        const YOUR_PHONE_NUMBER_WITH_COUNTRY_CODE = '555184672843';
                        const YOUR_API_KEY = '9113901'; // Sua API Key aqui

                        console.log(`Número de WhatsApp correspondente encontrado: ${cleanedPhone}. Enviando notificação.`);
                        validContactsFound++;
                        notificationPromises.push(sendCallMeBotWhatsapp(YOUR_PHONE_NUMBER_WITH_COUNTRY_CODE, YOUR_API_KEY, msg));
                    } else {
                        console.warn(`Contato ${contact.name} (${contact.detail}) é um telefone, mas não corresponde ao número configurado com API Key. Pulando WhatsApp.`);
                    }
                }
                // --- FIM DA MODIFICAÇÃO ---
                else {
                    console.log(`Contato ${contact.name} (${contact.detail}) ignorado (não é Telegram @usuario nem o telefone configurado).`);
                }
            });

            if (validContactsFound === 0) {
                console.log("Nenhum contato válido encontrado para notificação via CallMeBot.");
                showMessage("Nenhum contato no formato @usuario (Telegram) ou o seu nº de WhatsApp foi encontrado para notificação automática.", true);
                return;
            }

            console.log(`Aguardando envio de ${notificationPromises.length} notificações via CallMeBot...`);
            const results = await Promise.all(notificationPromises);
            const successCount = results.filter(success => success === true).length;

            if (successCount > 0) {
                showMessage(`✅ Tentativa de notificação enviada para ${successCount} contato(s) (Telegram/WhatsApp).`);
            } else {
                //showMessage(`⚠️ Falha ao tentar notificar contatos. Verifique o console ou as autorizações do bot.`, true);
            }

        } else {
            console.log("Nenhum contato de confiança cadastrado para notificar via CallMeBot.");
            showMessage("Nenhum contato cadastrado. Adicione contatos na tela inicial antes.", true);
        }
    } catch (error) {
        console.error("Erro ao buscar contatos no Firebase para CallMeBot:", error);
        showMessage("Erro ao buscar contatos para notificar. Verifique sua conexão.", true);
    }
}
// ===================================================================================
// --- FIM DA FUNCIONALIDADE CALLMEBOT ---
// ===================================================================================


// --- Lógica de Contatos de Confiança (Gerenciamento Local) ---

/** Adiciona um novo contato de confiança no Firebase. */
async function handleAddEmergencyContact() {
    if (!currentUserId) { showMessage("Faça login para adicionar contatos.", true); return; }

    const name = ui.contactNameInput.value.trim();
    const rawDetail = ui.contactDetailInput.value.trim();
    const cleanedDetail = rawDetail.replace(/\D/g, ''); // Para validação de telefone

    ui.contactDetailInput.classList.remove('is-invalid'); // Limpa erro anterior

    if (!name || !rawDetail) {
        showMessage("Preencha o nome e o detalhe (Telefone ou @usuario Telegram) do contato.", true);
        return;
    }

    // Valida se é Telefone OU Telegram OU Email (Email não será usado para CallMeBot)
    if (!isValidPhone(cleanedDetail) && !isValidTelegramUsername(rawDetail) && !isValidEmail(rawDetail)) {
        ui.contactDetailInput.classList.add('is-invalid');
        showMessage("Formato inválido. Use um Telefone BR (10/11 dígitos), um @usuario Telegram ou um email.", true);
        return;
    }

    // Salva o 'rawDetail' que pode conter máscara, @, ou ser email
    const detailToSave = rawDetail;

    showLoader();
    try {
        await push(ref(db, `users/${currentUserId}/emergencyContacts`), { name, detail: detailToSave });
        showMessage("Contato adicionado com sucesso!");
        ui.contactNameInput.value = '';
        ui.contactDetailInput.value = ''; // Limpa o campo após salvar
        ui.contactDetailInput.classList.remove('is-invalid');
    } catch (error) {
        console.error("Erro ao adicionar contato:", error);
        showMessage("Erro ao adicionar contato: " + error.message, true);
    } finally {
        hideLoader();
    }
}

/** Remove um contato de confiança do Firebase. */
async function handleRemoveEmergencyContact(e) {
    // Impede que o evento se propague, caso o botão esteja dentro de outro elemento clicável
    e.stopPropagation();

    const contactId = e.currentTarget.dataset.id;
    if (!currentUserId || !contactId) {
         console.error("Não foi possível remover contato: ID do usuário ou contato ausente.");
         return;
    }

    // ADICIONADO: Confirmação visual antes de remover (substitui confirm())
    const contactElement = e.currentTarget.closest('.d-flex'); // Encontra o elemento pai
    const contactName = contactElement?.querySelector('.text-break')?.textContent?.split('(')[0]?.trim() || 'este contato';

    // REMOVIDO: Prompt que pode falhar em iframes
    // if (prompt(`Tem certeza que deseja remover "${contactName}"? Digite 'sim' para confirmar.`)?.toLowerCase() !== 'sim') {
    //     console.log("Remoção cancelada pelo usuário.");
    //     return;
    // }
    console.warn(`Removendo contato ${contactName} (${contactId}) - Confirmação pulada.`); // Adiciona log

    showLoader();
    try {
        await remove(ref(db, `users/${currentUserId}/emergencyContacts/${contactId}`));
        showMessage("Contato removido.");
        // A UI será atualizada automaticamente pelo listener onValue
    } catch (error) {
        console.error("Erro ao remover contato:", error);
        showMessage("Erro ao remover contato: " + error.message, true);
    } finally {
        hideLoader();
    }
}

/** * @function loadEmergencyContacts
 * Carrega e exibe a lista de contatos de confiança, atualizando em tempo real.
 * (MODIFICADO PELO PATCH SEÇÃO 3)
 */
async function loadEmergencyContacts(userId) {
    if(userId) currentUserId = userId;
    if (!currentUserId || !ui.contactsListDiv) {
         console.warn("Não foi possível carregar contatos: ID do usuário ou div da lista não encontrados.");
         return;
    }

    const contactsRef = ref(db, `users/${currentUserId}/emergencyContacts`);

    // --- PATCH: SEÇÃO 3 ---
    // Garante que o listener antigo seja removido antes de adicionar um novo.
    if (contactsListener) {
        try {
             off(contactsRef, 'value', contactsListener);
             console.log("Removendo listener de contatos antigo.");
        } catch(e) {
             console.error("Erro ao tentar remover listener de contatos antigo:", e);
        }
        contactsListener = null; // Garante que a variável seja limpa
    }
    // ----------------------------

    console.log("Adicionando listener para contatos...");
    // MODIFICADO: Armazena o listener na variável
    contactsListener = onValue(contactsRef, (snapshot) => {
        // Verifica novamente se o elemento ainda existe
        if (!ui.contactsListDiv) {
             console.warn("Div da lista de contatos não encontrada no momento da atualização.");
             // Tenta remover o listener se a div sumiu
             if (contactsListener) {
                  try {
                       off(contactsRef, 'value', contactsListener);
                       console.log("Div sumiu, removendo listener de contatos.");
                  } catch(e) {
                       console.error("Erro ao remover listener após div sumir:", e);
                  }
                  contactsListener = null;
             }
             return;
        }

        ui.contactsListDiv.innerHTML = '';
        let contactsFound = false;

        if (snapshot.exists()) {
            contactsFound = true;
            snapshot.forEach(childSnapshot => {
                const contact = { id: childSnapshot.key, ...childSnapshot.val() };

                // Validação defensiva: garante que o contato tem id e detail
                if (!contact.id || !contact.detail) {
                      console.warn("Contato inválido encontrado no Firebase (sem id ou detail):", childSnapshot.val());
                      return; // Pula este contato
                }

                const div = document.createElement('div');
                div.className = 'd-flex justify-content-between align-items-center p-2 rounded mb-1 small';
                // Sanitização básica (evitar XSS simples se nome/detail viesse de fontes não confiáveis)
                const safeName = contact.name ? contact.name.replace(/</g, "&lt;").replace(/>/g, "&gt;") : 'Nome Ausente';
                const safeDetail = contact.detail ? contact.detail.replace(/</g, "&lt;").replace(/>/g, "&gt;") : 'Detalhe Ausente';

                div.innerHTML = `
                    <span class="text-break me-2">${safeName} (${safeDetail})</span>
                    <button data-id="${contact.id}" class="btn btn-sm btn-link text-danger remove-contact-btn p-0 ms-auto flex-shrink-0" aria-label="Remover contato ${safeName}">
                        <i class="fas fa-trash"></i>
                    </button>`;
                ui.contactsListDiv.appendChild(div);

                // Adiciona listener DEPOIS de adicionar ao DOM
                const removeButton = div.querySelector('.remove-contact-btn');
                if (removeButton) {
                      removeButton.addEventListener('click', handleRemoveEmergencyContact);
                } else {
                      console.error("Botão de remover não encontrado para o contato:", contact.id);
                }
            });
        }

        if (!contactsFound) {
            ui.contactsListDiv.innerHTML = '<p class="text-muted-light small fst-italic">Nenhum contato de confiança adicionado.</p>';
        }
    }, (error) => {
        console.error("Erro ao carregar/ouvir contatos de emergência:", error);
        if (ui.contactsListDiv) {
            ui.contactsListDiv.innerHTML = '<p class="text-danger small">Erro ao carregar contatos. Verifique o console.</p>';
        }
        showMessage("Não foi possível carregar seus contatos de confiança.", true);
        // Tenta remover o listener em caso de erro persistente
        if (contactsListener) {
             try {
                 off(contactsRef, 'value', contactsListener);
                 console.log("Erro ao carregar, removendo listener de contatos.");
             } catch(e) {
                 console.error("Erro ao remover listener após falha no carregamento:", e);
             }
             contactsListener = null;
        }
    });
}
