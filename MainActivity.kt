package com.bristi.controller

import android.Manifest
import android.annotation.SuppressLint
import android.app.Activity
import android.bluetooth.BluetoothAdapter
import android.bluetooth.BluetoothDevice
import android.bluetooth.BluetoothGatt
import android.bluetooth.BluetoothGattCallback
import android.bluetooth.BluetoothGattCharacteristic
import android.bluetooth.BluetoothGattDescriptor
import android.bluetooth.BluetoothManager
import android.bluetooth.BluetoothProfile
import android.bluetooth.BluetoothSocket
import android.bluetooth.le.BluetoothLeScanner
import android.bluetooth.le.ScanCallback
import android.bluetooth.le.ScanResult
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.content.SharedPreferences
import android.content.pm.PackageManager
import android.net.ConnectivityManager
import android.net.NetworkCapabilities
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.speech.RecognitionListener
import android.speech.RecognizerIntent
import android.speech.SpeechRecognizer
import android.speech.tts.TextToSpeech
import android.speech.tts.UtteranceProgressListener
import android.util.Log
import android.webkit.JavascriptInterface
import android.webkit.WebView
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.compose.setContent
import androidx.activity.result.contract.ActivityResultContracts
import androidx.compose.animation.core.*
import androidx.compose.foundation.BorderStroke
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.Image
import androidx.compose.foundation.background
import androidx.compose.foundation.border
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.foundation.lazy.items
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Bluetooth
import androidx.compose.material.icons.outlined.Person
import androidx.compose.material.icons.outlined.Settings
import androidx.compose.material3.*
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.draw.scale
import androidx.compose.ui.draw.shadow
import androidx.compose.ui.graphics.*
import androidx.compose.ui.graphics.drawscope.Stroke
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.platform.LocalHapticFeedback
import androidx.compose.ui.hapticfeedback.HapticFeedbackType
import androidx.compose.ui.res.painterResource
import androidx.compose.ui.text.TextStyle
import androidx.compose.ui.text.font.FontFamily
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import androidx.compose.ui.viewinterop.AndroidView
import androidx.compose.ui.window.Dialog
import androidx.core.content.ContextCompat
import com.google.ai.client.generativeai.GenerativeModel
import com.google.ai.client.generativeai.type.content
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext
import java.io.IOException
import java.io.InputStream
import java.io.OutputStream
import java.util.*
import kotlin.math.sin

// ─────────────────────────────────────────────────────────────────────────────
//  App State & Design Tokens (Jasica AI Style)
// ─────────────────────────────────────────────────────────────────────────────

enum class AppState { IDLE, LISTENING, THINKING, SPEAKING }

val JasicaOrange  = Color(0xFFFF6B00)
val JasicaPurple  = Color(0xFF4A00E0)
val JasicaWhite   = Color(0xFFFFFFFF)
val JasicaCardBg  = Color(0x20FFFFFF)

val InterFontFamily = FontFamily.SansSerif

val AiModelsList = listOf("gemini-2.5-flash", "gemini-3.1-flash", "gemini-3.5-flash")

// ─────────────────────────────────────────────────────────────────────────────
//  MainActivity
// ─────────────────────────────────────────────────────────────────────────────

@SuppressLint("MissingPermission")
class MainActivity : ComponentActivity(), TextToSpeech.OnInitListener {

    // ── Config ────────────────────────────────────────────────────────────────
    // Make sure you have your API key set correctly
    private val DEFAULT_API_KEY = "YOUR_GEMINI_API_KEY" // Add your key or use BuildConfig
    private val SPP_UUID: UUID = UUID.fromString("00001101-0000-1000-8000-00805F9B34FB")
    private val CLIENT_CHARACTERISTIC_CONFIG = UUID.fromString("00002902-0000-1000-8000-00805f9b34fb")

    // ── Services ──────────────────────────────────────────────────────────────
    private lateinit var tts: TextToSpeech
    private lateinit var speechRecognizer: SpeechRecognizer
    private val mainHandler = Handler(Looper.getMainLooper())
    private lateinit var sharedPrefs: SharedPreferences
    private var currentAiJob: Job? = null

    // ── Bluetooth Architecture ────────────────────────────────────────────────
    private var btAdapter: BluetoothAdapter? = null
    private var bleScanner: BluetoothLeScanner? = null
    private var discoveryReceiver: BroadcastReceiver? = null
    private var pendingDevice: BluetoothDevice? = null

    // Classic Connection State
    private var classicSocket: BluetoothSocket? = null
    private var classicOutStream: OutputStream? = null
    private var classicInStream: InputStream? = null
    private var isClassicConnected = false

    // BLE Connection State
    private var bluetoothGatt: BluetoothGatt? = null
    private var bleWriteChar: BluetoothGattCharacteristic? = null
    private var bleNotifyChar: BluetoothGattCharacteristic? = null
    private var isBleConnected = false

    // ── UI State ──────────────────────────────────────────────────────────────
    private val appState         = mutableStateOf(AppState.IDLE)
    private val isBtConnected    = mutableStateOf(false)
    private val aiResponseText   = mutableStateOf("")
    private val pairedDevices    = mutableStateListOf<BluetoothDevice>()
    private val availableDevices = mutableStateListOf<BluetoothDevice>()
    private val deviceAddresses  = HashSet<String>()
    private val isScanning       = mutableStateOf(false)
    private val showDeviceDialog = mutableStateOf(false)
    private val showSettingsDialog= mutableStateOf(false)

    private val userApiKey       = mutableStateOf("")
    private val selectedAiModel  = mutableStateOf(AiModelsList[0])

    // ── Conversation Memory ───────────────────────────────────────────────────
    private val conversationHistory = mutableListOf<com.google.ai.client.generativeai.type.Content>()
    private val MAX_HISTORY_PAIRS   = 6

    // ── System Prompt ─────────────────────────────────────────────────────────
    private val systemInstruction = """
        You are Jasica AI.
        You serve Joy Kumbhakar.
        
        YOUR PERSONALITY:
        - Helpful, polite, intelligent, and highly capable.
        - You blend English and Bengali (Bangla) naturally.
        - Keep replies concise (150–200 characters).
        
        HARDWARE CONTROL INSTRUCTIONS:
        Parse device control intent and append the exact trigger at the VERY END. Never explain the command.
        - "Turn on all"                      -> [CMD:on]
        - "Turn off all"                     -> [CMD:off]
        - "Mood lighting / Turn on Mood"     -> [CMD:mood]
        - "Turn on PC / Computer"            -> [CMD:a]
        - "Turn off PC / Computer"           -> [CMD:A]
        - "Turn on RGB / Night light"        -> [CMD:b]
        - "Turn off RGB / Night light"       -> [CMD:B]
        - "Turn on White LED / Room light"   -> [CMD:c]
        - "Turn off White LED / Room light"  -> [CMD:C]
        - "Turn on Plug"                     -> [CMD:d]
        - "Turn off Plug"                    -> [CMD:D]
    """.trimIndent()

    // ─────────────────────────────────────────────────────────────────────────
    //  Local Command Table  (works OFFLINE)
    // ─────────────────────────────────────────────────────────────────────────

    private data class LocalCommand(
        val keywords : List<String>,
        val anyOf    : List<String> = emptyList(),
        val command  : String,
        val confirmationText: String
    )

    private val localCommandTable = listOf(
        LocalCommand(listOf("turn","on","all"),                         command = "on",   confirmationText = "Activating all systems."),
        LocalCommand(listOf("turn","off","all"),                        command = "off",  confirmationText = "Shutting everything down."),
        LocalCommand(listOf("mood"),                                    command = "mood", confirmationText = "Mood lighting on."),
        LocalCommand(listOf("turn","on"),  anyOf = listOf("pc","computer"), command = "a",confirmationText = "Booting the PC."),
        LocalCommand(listOf("turn","off"), anyOf = listOf("pc","computer"), command = "A",confirmationText = "PC shutting down."),
        LocalCommand(listOf("turn","on"),  anyOf = listOf("rgb","night"),   command = "b",confirmationText = "RGB lights on."),
        LocalCommand(listOf("turn","off"), anyOf = listOf("rgb","night"),   command = "B",confirmationText = "RGB off."),
        LocalCommand(listOf("turn","on"),  anyOf = listOf("white","room","led","light"), command = "c", confirmationText = "Room light on."),
        LocalCommand(listOf("turn","off"), anyOf = listOf("white","room","led","light"), command = "C", confirmationText = "Room light off."),
        LocalCommand(listOf("turn","on","plug"),                        command = "d",   confirmationText = "Plug switched on."),
        LocalCommand(listOf("turn","off","plug"),                       command = "D",   confirmationText = "Plug off.")
    )

    private fun matchLocalCommand(spokenText: String): LocalCommand? {
        val words = spokenText
            .lowercase(Locale.getDefault())
            .replace(Regex("[^a-z0-9 ]"), " ")
            .split("\\s+".toRegex())
            .filter { it.isNotBlank() }
            .toSet()

        return localCommandTable.firstOrNull { cmd ->
            val allKeywords = cmd.keywords.all { it in words }
            val anyOfMatch  = cmd.anyOf.isEmpty() || cmd.anyOf.any { it in words }
            allKeywords && anyOfMatch
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    //  Permissions & Intents
    // ─────────────────────────────────────────────────────────────────────────

    private val requestPermissionsLauncher = registerForActivityResult(
        ActivityResultContracts.RequestMultiplePermissions()
    ) { permissions ->
        val audioGranted = permissions[Manifest.permission.RECORD_AUDIO] == true
        if (audioGranted) {
            setupSpeechRecognizer()
        } else {
            Toast.makeText(this, "Microphone permission required", Toast.LENGTH_SHORT).show()
        }
    }

    private val enableBluetoothLauncher = registerForActivityResult(
        ActivityResultContracts.StartActivityForResult()
    ) { result ->
        if (result.resultCode == Activity.RESULT_OK) {
            loadPairedDevices()
            showDeviceDialog.value = true
        } else {
            Toast.makeText(this, "Bluetooth must be enabled to connect.", Toast.LENGTH_SHORT).show()
        }
    }

    private fun hasBluetoothPermissions(): Boolean {
        return if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            ContextCompat.checkSelfPermission(this, Manifest.permission.BLUETOOTH_CONNECT) == PackageManager.PERMISSION_GRANTED &&
                    ContextCompat.checkSelfPermission(this, Manifest.permission.BLUETOOTH_SCAN) == PackageManager.PERMISSION_GRANTED
        } else {
            ContextCompat.checkSelfPermission(this, Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    //  Lifecycle
    // ─────────────────────────────────────────────────────────────────────────

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        sharedPrefs = getSharedPreferences("JasicaSettings", Context.MODE_PRIVATE)
        userApiKey.value = sharedPrefs.getString("API_KEY", DEFAULT_API_KEY) ?: DEFAULT_API_KEY
        selectedAiModel.value = sharedPrefs.getString("AI_MODEL", AiModelsList[0]) ?: AiModelsList[0]

        tts = TextToSpeech(this, this)

        val bluetoothManager = getSystemService(Context.BLUETOOTH_SERVICE) as BluetoothManager
        btAdapter = bluetoothManager.adapter
        bleScanner = btAdapter?.bluetoothLeScanner

        setupBluetoothReceiver()

        requestPermissionsLauncher.launch(
            arrayOf(
                Manifest.permission.RECORD_AUDIO,
                Manifest.permission.BLUETOOTH_CONNECT,
                Manifest.permission.BLUETOOTH_SCAN,
                Manifest.permission.ACCESS_FINE_LOCATION,
                Manifest.permission.ACCESS_COARSE_LOCATION
            )
        )

        setContent {
            JasicaTheme {
                JasicaScreen(
                    appState         = appState.value,
                    isBtConnected    = isBtConnected.value,
                    responseText     = aiResponseText.value,
                    pairedDevices    = pairedDevices,
                    availableDevices = availableDevices,
                    isScanning       = isScanning.value,
                    showDialog       = showDeviceDialog.value,
                    showSettings     = showSettingsDialog.value,
                    currentApiKey    = userApiKey.value,
                    currentModel     = selectedAiModel.value,
                    onMicTap         = {
                        if (appState.value != AppState.LISTENING) {
                            startListening()
                        }
                    },
                    onBtIconTap      = { checkAndEnableBluetooth() },
                    onSettingsTap    = { showSettingsDialog.value = true },
                    onDeviceSelect   = { device -> handleDeviceSelection(device) },
                    onScanTap        = { startScans() },
                    onDismissDialog  = { showDeviceDialog.value = false; stopScans() },
                    onDismissSettings= { showSettingsDialog.value = false },
                    onSaveSettings   = { newKey, newModel ->
                        userApiKey.value = newKey
                        selectedAiModel.value = newModel
                        sharedPrefs.edit()
                            .putString("API_KEY", newKey)
                            .putString("AI_MODEL", newModel)
                            .apply()
                        showSettingsDialog.value = false
                        Toast.makeText(this, "Settings Saved.", Toast.LENGTH_SHORT).show()
                    },
                    onHtmlCardTap    = { action ->
                        // This handles the clicks coming from the WebView
                        runOnUiThread {
                            Toast.makeText(this, "Triggered: $action", Toast.LENGTH_SHORT).show()
                        }
                    }
                )
            }
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        currentAiJob?.cancel()
        if (::tts.isInitialized) tts.shutdown()
        if (::speechRecognizer.isInitialized) speechRecognizer.destroy()
        disconnectAll()
        discoveryReceiver?.let { try { unregisterReceiver(it) } catch (e: Exception) {} }
    }

    // ─────────────────────────────────────────────────────────────────────────
    //  Network & Speech
    // ─────────────────────────────────────────────────────────────────────────
    private fun isNetworkAvailable(): Boolean {
        val connectivityManager = getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
        val network = connectivityManager.activeNetwork ?: return false
        val activeNetwork = connectivityManager.getNetworkCapabilities(network) ?: return false
        return activeNetwork.hasTransport(NetworkCapabilities.TRANSPORT_WIFI) ||
                activeNetwork.hasTransport(NetworkCapabilities.TRANSPORT_CELLULAR)
    }

    override fun onInit(status: Int) {
        if (status == TextToSpeech.SUCCESS) {
            tts.language = Locale("en", "US") // Female voice for Jasica
            tts.setPitch(1.1f)

            tts.setOnUtteranceProgressListener(object : UtteranceProgressListener() {
                override fun onStart(utteranceId: String?) {}
                override fun onDone(utteranceId: String?)  {
                    runOnUiThread {
                        if (appState.value == AppState.SPEAKING) {
                            appState.value = AppState.IDLE
                        }
                    }
                }
                override fun onError(utteranceId: String?) {
                    runOnUiThread {
                        if (appState.value == AppState.SPEAKING) {
                            appState.value = AppState.IDLE
                        }
                    }
                }
            })
        }
    }

    private fun setupSpeechRecognizer() {
        speechRecognizer = SpeechRecognizer.createSpeechRecognizer(this)
        speechRecognizer.setRecognitionListener(object : RecognitionListener {
            override fun onReadyForSpeech(params: Bundle?) {
                appState.value = AppState.LISTENING
                aiResponseText.value = ""
            }
            override fun onBeginningOfSpeech() {}
            override fun onRmsChanged(rmsdB: Float) {}
            override fun onBufferReceived(buffer: ByteArray?) {}
            override fun onEndOfSpeech() { appState.value = AppState.THINKING }
            override fun onError(error: Int) {
                appState.value = AppState.IDLE
                Toast.makeText(this@MainActivity, "Audio error: $error", Toast.LENGTH_SHORT).show()
            }
            override fun onResults(results: Bundle?) {
                val matches = results?.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION)
                if (!matches.isNullOrEmpty()) {
                    routeVoiceCommand(matches[0])
                } else {
                    appState.value = AppState.IDLE
                }
            }
            override fun onPartialResults(partialResults: Bundle?) {}
            override fun onEvent(eventType: Int, params: Bundle?) {}
        })
    }

    private fun startListening() {
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED) {
            currentAiJob?.cancel()
            if (tts.isSpeaking) tts.stop()
            aiResponseText.value = ""
            try {
                speechRecognizer.stopListening()
                speechRecognizer.cancel()
            } catch (e: Exception) {}

            val intent = Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH).apply {
                putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM)
                putExtra(RecognizerIntent.EXTRA_LANGUAGE, Locale.getDefault())
            }
            speechRecognizer.startListening(intent)
        } else {
            Toast.makeText(this, "Mic permission required", Toast.LENGTH_SHORT).show()
        }
    }

    private fun routeVoiceCommand(spokenText: String) {
        val localMatch = matchLocalCommand(spokenText)
        if (localMatch != null) {
            if (localMatch.command.isNotEmpty()) {
                sendCommandOverBluetooth(localMatch.command)
            }
            runOnUiThread {
                aiResponseText.value = localMatch.confirmationText
                appState.value = AppState.SPEAKING
                tts.speak(localMatch.confirmationText, TextToSpeech.QUEUE_FLUSH, null, "JASICA_LOCAL")
            }
        } else {
            sendToGemini(spokenText)
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    //  Gemini AI
    // ─────────────────────────────────────────────────────────────────────────

    private fun sendToGemini(prompt: String) {
        if (!isNetworkAvailable()) {
            handleAIResponse("I am currently offline. Please check the network connection.")
            return
        }

        val activeApiKey = (if (userApiKey.value.isNotBlank()) userApiKey.value else DEFAULT_API_KEY).trim()
        if (activeApiKey.isBlank()) {
            handleAIResponse("My API key is missing. Please update it in settings.")
            return
        }

        appState.value = AppState.THINKING
        currentAiJob?.cancel()

        currentAiJob = CoroutineScope(Dispatchers.IO).launch {
            try {
                val model = GenerativeModel(
                    modelName        = selectedAiModel.value,
                    apiKey           = activeApiKey,
                    systemInstruction = content { text(systemInstruction) }
                )

                val delays = listOf(1000L, 2000L, 4000L, 8000L, 16000L)
                var reply = ""
                var success = false

                for (delayTime in delays) {
                    try {
                        val chat = model.startChat(history = conversationHistory.toList())
                        val response = chat.sendMessage(prompt)
                        reply = response.text ?: "Uh oh, something went wrong."
                        success = true
                        break
                    } catch (e: CancellationException) {
                        throw e
                    } catch (e: Exception) {
                        delay(delayTime)
                    }
                }

                if (!success) {
                    throw Exception("API connection failed.")
                }

                conversationHistory.add(content(role = "user")  { text(prompt) })
                conversationHistory.add(content(role = "model") { text(reply)  })

                while (conversationHistory.size > MAX_HISTORY_PAIRS * 2) {
                    conversationHistory.removeAt(0)
                    conversationHistory.removeAt(0)
                }

                handleAIResponse(reply)

            } catch (e: CancellationException) {
            } catch (e: Exception) {
                withContext(Dispatchers.Main) { Log.e("JasicaApp", "API Error", e) }
                handleAIResponse("Server connection failed. Check network stability.")
            }
        }
    }

    private fun handleAIResponse(rawReply: String) {
        val regex  = "\\[CMD:(.*?)\\]".toRegex()
        val match  = regex.find(rawReply)
        var speech = rawReply

        if (match != null) {
            sendCommandOverBluetooth(match.groupValues[1])
            speech = rawReply.replace(regex, "").trim()
        }

        runOnUiThread {
            aiResponseText.value = speech
            appState.value = AppState.SPEAKING
            tts.speak(speech, TextToSpeech.QUEUE_FLUSH, null, "JASICA_REPLY")
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    //  Bluetooth Device Management (Keep Original Logic)
    // ─────────────────────────────────────────────────────────────────────────

    private fun checkAndEnableBluetooth() {
        if (!hasBluetoothPermissions()) {
            Toast.makeText(this, "Bluetooth permissions missing.", Toast.LENGTH_LONG).show()
            return
        }
        if (btAdapter?.isEnabled == false) {
            val enableBtIntent = Intent(BluetoothAdapter.ACTION_REQUEST_ENABLE)
            enableBluetoothLauncher.launch(enableBtIntent)
        } else {
            loadPairedDevices()
            showDeviceDialog.value = true
        }
    }

    private fun loadPairedDevices() {
        if (!hasBluetoothPermissions()) return
        pairedDevices.clear()
        try {
            if (btAdapter?.isEnabled == true) {
                btAdapter?.bondedDevices?.let { pairedDevices.addAll(it) }
            }
        } catch (e: SecurityException) {}
    }

    private fun addDevice(device: BluetoothDevice?) {
        if (device != null && device.address != null) {
            if (deviceAddresses.add(device.address)) {
                availableDevices.add(device)
            }
        }
    }

    private val bleScanCallback = object : ScanCallback() {
        override fun onScanResult(callbackType: Int, result: ScanResult) {
            addDevice(result.device)
        }
    }

    @SuppressLint("UnspecifiedRegisterReceiverFlag")
    private fun setupBluetoothReceiver() {
        discoveryReceiver = object : BroadcastReceiver() {
            override fun onReceive(context: Context, intent: Intent) {
                when (intent.action) {
                    BluetoothDevice.ACTION_FOUND -> {
                        addDevice(intent.getParcelableExtra<BluetoothDevice>(BluetoothDevice.EXTRA_DEVICE))
                    }
                    BluetoothAdapter.ACTION_DISCOVERY_STARTED  -> isScanning.value = true
                    BluetoothAdapter.ACTION_DISCOVERY_FINISHED -> isScanning.value = false
                    BluetoothDevice.ACTION_BOND_STATE_CHANGED  -> {
                        val device = intent.getParcelableExtra<BluetoothDevice>(BluetoothDevice.EXTRA_DEVICE)
                        val state  = intent.getIntExtra(BluetoothDevice.EXTRA_BOND_STATE, BluetoothDevice.ERROR)

                        if (state == BluetoothDevice.BOND_BONDED && device != null) {
                            loadPairedDevices()
                            if (pendingDevice?.address == device.address) {
                                val devToConnect = pendingDevice!!
                                pendingDevice = null
                                proceedWithConnection(devToConnect)
                            }
                        } else if (state == BluetoothDevice.BOND_NONE && device != null) {
                            if (pendingDevice?.address == device.address) {
                                val devToConnect = pendingDevice!!
                                pendingDevice = null
                                proceedWithConnection(devToConnect)
                            }
                        }
                    }
                }
            }
        }
        val filter = IntentFilter().apply {
            addAction(BluetoothDevice.ACTION_FOUND)
            addAction(BluetoothAdapter.ACTION_DISCOVERY_STARTED)
            addAction(BluetoothAdapter.ACTION_DISCOVERY_FINISHED)
            addAction(BluetoothDevice.ACTION_BOND_STATE_CHANGED)
        }
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
            registerReceiver(discoveryReceiver, filter, Context.RECEIVER_NOT_EXPORTED)
        } else {
            registerReceiver(discoveryReceiver, filter)
        }
    }

    private fun startScans() {
        if (!hasBluetoothPermissions()) return
        try {
            if (btAdapter?.isEnabled == true) {
                availableDevices.clear()
                deviceAddresses.clear()
                bleScanner?.startScan(bleScanCallback)
                if (btAdapter?.isDiscovering == true) btAdapter?.cancelDiscovery()
                btAdapter?.startDiscovery()
            } else {
                checkAndEnableBluetooth()
            }
        } catch(e: SecurityException) {}
    }

    private fun stopScans() {
        try {
            bleScanner?.stopScan(bleScanCallback)
            if (btAdapter?.isDiscovering == true) btAdapter?.cancelDiscovery()
        } catch(e: SecurityException) {}
    }

    private fun handleDeviceSelection(device: BluetoothDevice) {
        stopScans()
        disconnectAll()

        if (device.type == BluetoothDevice.DEVICE_TYPE_LE) {
            proceedWithConnection(device)
        } else {
            try {
                if (device.bondState == BluetoothDevice.BOND_BONDING) {
                    pendingDevice = device
                } else if (device.bondState != BluetoothDevice.BOND_BONDED) {
                    pendingDevice = device
                    val bondingStarted = try { device.createBond() } catch (e: Exception) { false }
                    if (!bondingStarted) {
                        pendingDevice = null
                        proceedWithConnection(device)
                    }
                } else {
                    proceedWithConnection(device)
                }
            } catch (e: SecurityException) {}
        }
    }

    private fun proceedWithConnection(device: BluetoothDevice) {
        try { Toast.makeText(this, "Connecting...", Toast.LENGTH_SHORT).show() } catch (e: SecurityException) {}
        showDeviceDialog.value = false

        if (device.type == BluetoothDevice.DEVICE_TYPE_LE) connectBLE(device) else connectClassic(device)
    }

    private fun connectBLE(device: BluetoothDevice) {
        val gattCallback = object : BluetoothGattCallback() {
            override fun onConnectionStateChange(gatt: BluetoothGatt, status: Int, newState: Int) {
                if (newState == BluetoothProfile.STATE_CONNECTED) {
                    mainHandler.postDelayed({ try { gatt.discoverServices() } catch (e: SecurityException) {} }, 600)
                } else if (newState == BluetoothProfile.STATE_DISCONNECTED) {
                    isBleConnected = false
                    runOnUiThread { isBtConnected.value = false }
                    gatt.close()
                }
            }
            override fun onServicesDiscovered(gatt: BluetoothGatt, status: Int) {
                if (status == BluetoothGatt.GATT_SUCCESS) {
                    bleWriteChar = null
                    bleNotifyChar = null

                    for (service in gatt.services) {
                        for (characteristic in service.characteristics) {
                            val props = characteristic.properties
                            if ((props and BluetoothGattCharacteristic.PROPERTY_WRITE) != 0 || (props and BluetoothGattCharacteristic.PROPERTY_WRITE_NO_RESPONSE) != 0) {
                                if (bleWriteChar == null) {
                                    bleWriteChar = characteristic
                                    bleWriteChar?.writeType = if ((props and BluetoothGattCharacteristic.PROPERTY_WRITE_NO_RESPONSE) != 0) BluetoothGattCharacteristic.WRITE_TYPE_NO_RESPONSE else BluetoothGattCharacteristic.WRITE_TYPE_DEFAULT
                                }
                            }
                        }
                    }
                    if (bleWriteChar != null) {
                        isBleConnected = true
                        runOnUiThread { isBtConnected.value = true; Toast.makeText(this@MainActivity, "BLE Connected", Toast.LENGTH_SHORT).show() }
                    } else {
                        gatt.disconnect()
                    }
                }
            }
        }
        try {
            bluetoothGatt = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                device.connectGatt(this, false, gattCallback, BluetoothDevice.TRANSPORT_LE)
            } else {
                device.connectGatt(this, false, gattCallback)
            }
        } catch (e: SecurityException) {}
    }

    private fun connectClassic(device: BluetoothDevice) {
        CoroutineScope(Dispatchers.IO).launch {
            try {
                @SuppressLint("MissingPermission")
                if (btAdapter?.isDiscovering == true) btAdapter?.cancelDiscovery()
                delay(300)
                classicSocket = device.createInsecureRfcommSocketToServiceRecord(SPP_UUID)
                classicSocket?.connect()
            } catch (e: IOException) {
                try { classicSocket?.close() } catch (ignored: IOException) {}
                try {
                    @Suppress("DiscouragedPrivateApi")
                    val method = device.javaClass.getMethod("createRfcommSocket", Int::class.java)
                    classicSocket = method.invoke(device, 1) as BluetoothSocket
                    classicSocket?.connect()
                } catch (e2: Exception) {
                    classicSocket = null
                }
            } catch (e: SecurityException) {
                return@launch
            }

            if (classicSocket != null && classicSocket!!.isConnected) {
                isClassicConnected = true
                classicOutStream = classicSocket?.outputStream
                classicInStream = classicSocket?.inputStream
                withContext(Dispatchers.Main) { isBtConnected.value = true; Toast.makeText(this@MainActivity, "Connected", Toast.LENGTH_SHORT).show() }

                val buffer = ByteArray(1024)
                while (isClassicConnected) {
                    try { if ((classicInStream?.read(buffer) ?: -1) < 0) break } catch (e: IOException) { break }
                }
                isClassicConnected = false
                withContext(Dispatchers.Main) { isBtConnected.value = false }
            }
        }
    }

    private fun disconnectAll() {
        if (bluetoothGatt != null) { try { bluetoothGatt?.disconnect(); bluetoothGatt?.close() } catch (e: SecurityException) {}; bluetoothGatt = null }
        isBleConnected = false
        if (classicSocket != null) { try { classicSocket?.close() } catch (e: IOException) {}; classicSocket = null }
        isClassicConnected = false
        runOnUiThread { isBtConnected.value = false }
    }

    private fun sendCommandOverBluetooth(command: String) {
        val payload = "$command\n".toByteArray()
        if (isClassicConnected && classicOutStream != null) {
            CoroutineScope(Dispatchers.IO).launch { try { classicOutStream?.write(payload); classicOutStream?.flush() } catch (e: IOException) { disconnectAll() } }
        } else if (isBleConnected && bluetoothGatt != null && bleWriteChar != null) {
            try { bleWriteChar?.value = payload; bluetoothGatt?.writeCharacteristic(bleWriteChar) } catch (e: SecurityException) {}
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  Theme & Jetpack Compose UI
// ─────────────────────────────────────────────────────────────────────────────

@Composable
fun JasicaTheme(content: @Composable () -> Unit) {
    MaterialTheme(
        colorScheme = darkColorScheme(
            background = Color.Black,
            surface    = Color(0xFF121212),
            primary    = JasicaPurple,
            onPrimary  = JasicaWhite,
            secondary  = JasicaOrange
        ),
        content = content
    )
}

@Composable
fun JasicaScreen(
    appState         : AppState,
    isBtConnected    : Boolean,
    responseText     : String,
    pairedDevices    : List<BluetoothDevice>,
    availableDevices : List<BluetoothDevice>,
    isScanning       : Boolean,
    showDialog       : Boolean,
    showSettings     : Boolean,
    currentApiKey    : String,
    currentModel     : String,
    onMicTap         : () -> Unit,
    onBtIconTap      : () -> Unit,
    onSettingsTap    : () -> Unit,
    onDeviceSelect   : (BluetoothDevice) -> Unit,
    onScanTap        : () -> Unit,
    onDismissDialog  : () -> Unit,
    onDismissSettings: () -> Unit,
    onSaveSettings   : (String, String) -> Unit,
    onHtmlCardTap    : (String) -> Unit
) {
    Box(modifier = Modifier.fillMaxSize()) {
        // 1. Full Screen Generated Background
        Image(
            painter = painterResource(id = R.drawable.generated_bg), // Your uploaded orange/purple bg
            contentDescription = "Background",
            modifier = Modifier.fillMaxSize(),
            contentScale = ContentScale.Crop
        )

        Column(
            modifier = Modifier.fillMaxSize(),
            horizontalAlignment = Alignment.CenterHorizontally
        ) {
            // 2. Header Status Bar
            Row(
                modifier = Modifier
                    .fillMaxWidth()
                    .padding(horizontal = 24.dp, vertical = 20.dp),
                horizontalArrangement = Arrangement.SpaceBetween,
                verticalAlignment = Alignment.CenterVertically
            ) {
                // Logo & Title
                Row(verticalAlignment = Alignment.CenterVertically) {
                    Image(
                        painter = painterResource(id = R.drawable.jasica),
                        contentDescription = "Jasica Logo",
                        modifier = Modifier
                            .size(26.dp)
                            .clip(CircleShape)
                    )
                    Spacer(modifier = Modifier.width(10.dp))
                    Text(
                        text = "JASICA AI",
                        color = JasicaWhite,
                        fontFamily = InterFontFamily,
                        fontWeight = FontWeight.ExtraBold,
                        fontSize = 17.sp,
                        letterSpacing = 0.3.sp
                    )
                }

                // Settings & Bluetooth Connect (mapped to the user profile icon style)
                Row(verticalAlignment = Alignment.CenterVertically) {
                    IconButton(onClick = onSettingsTap) {
                        Icon(
                            imageVector = Icons.Outlined.Settings,
                            contentDescription = "Settings",
                            tint = JasicaWhite
                        )
                    }
                    Spacer(modifier = Modifier.width(4.dp))
                    // Using person icon as requested by the design, but it maps to Bluetooth logic
                    IconButton(onClick = onBtIconTap) {
                        Icon(
                            imageVector = if (isBtConnected) Icons.Default.Bluetooth else Icons.Outlined.Person,
                            contentDescription = "Bluetooth / Profile",
                            tint = JasicaWhite
                        )
                    }
                }
            }

            // 3. Main Title & Subtitle
            Spacer(modifier = Modifier.height(10.dp))
            Text(
                text = "JASICA AI",
                color = JasicaWhite,
                fontFamily = InterFontFamily,
                fontWeight = FontWeight.ExtraBold,
                fontSize = 44.sp,
                style = TextStyle(
                    shadow = Shadow(color = Color.Black.copy(alpha = 0.15f), offset = Offset(0f, 4f), blurRadius = 15f)
                )
            )
            Text(
                text = "Say \"Hey Jasica\" or tap below",
                color = JasicaWhite.copy(alpha = 0.85f),
                fontFamily = InterFontFamily,
                fontWeight = FontWeight.Medium,
                fontSize = 16.sp
            )

            // 4. Center Graphic (Wave + Floating Orb)
            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .weight(1f)
                    .padding(vertical = 10.dp),
                contentAlignment = Alignment.Center
            ) {
                // Animated Glowing Wave Canvas
                AudioWaveform(modifier = Modifier.fillMaxWidth().height(160.dp))

                // Floating Orb
                val infiniteTransition = rememberInfiniteTransition()
                val floatOffsetY by infiniteTransition.animateFloat(
                    initialValue = -12f,
                    targetValue = 12f,
                    animationSpec = infiniteRepeatable(tween(3000, easing = SineEasing), RepeatMode.Reverse)
                )

                Image(
                    painter = painterResource(id = R.drawable.jasica),
                    contentDescription = "Jasica Core",
                    modifier = Modifier
                        .size(280.dp)
                        .offset(y = floatOffsetY.dp)
                )
            }

            // 5. Dynamic Tagline / AI Response Text
            Text(
                text = if (responseText.isEmpty()) "Control your digital world\nwith your voice." else responseText,
                color = if (responseText.isEmpty()) JasicaWhite.copy(alpha = 0.85f) else JasicaWhite,
                fontFamily = InterFontFamily,
                fontWeight = if (responseText.isEmpty()) FontWeight.Medium else FontWeight.SemiBold,
                fontSize = 16.sp,
                textAlign = TextAlign.Center,
                modifier = Modifier.padding(horizontal = 30.dp, vertical = 20.dp)
            )

            // 6. WebView Glassmorphism Cards (Fulfilled specific user constraint)
            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .padding(horizontal = 20.dp, vertical = 10.dp)
                    .height(100.dp)
            ) {
                WebViewActionCards(onHtmlCardTap)
            }

            // 7. Bottom Mic Button
            Spacer(modifier = Modifier.height(10.dp))
            BottomMicButton(appState = appState, onClick = onMicTap)
            Spacer(modifier = Modifier.height(35.dp))
        }

        // Dialogs
        if (showDialog) {
            DeviceSelectionDialog(pairedDevices, availableDevices, isScanning, onDeviceSelect, onScanTap, onDismissDialog)
        }
        if (showSettings) {
            SettingsDialog(currentApiKey, currentModel, onDismissSettings, onSaveSettings)
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  Animated Components (Wave & Mic)
// ─────────────────────────────────────────────────────────────────────────────

@Composable
fun AudioWaveform(modifier: Modifier = Modifier) {
    val infiniteTransition = rememberInfiniteTransition()
    val phase by infiniteTransition.animateFloat(
        initialValue = 0f, targetValue = 2f * Math.PI.toFloat(),
        animationSpec = infiniteRepeatable(tween(4000, easing = LinearEasing), RepeatMode.Restart)
    )

    Canvas(modifier = modifier) {
        val width = size.width
        val height = size.height
        val centerY = height / 2

        // Draw multiple glowing strands like the HTML SVG
        for (i in 0..3) {
            val path = Path()
            path.moveTo(0f, centerY)
            val amplitude = if (i % 2 == 0) 40f else 60f
            val frequency = if (i < 2) 2f else 3f
            val phaseShift = i * (Math.PI.toFloat() / 2f)

            for (x in 0..width.toInt() step 10) {
                val normalizedX = x / width
                // Fade out edges smoothly
                val edgeMute = sin(normalizedX * Math.PI).toFloat()
                val y = centerY + sin((normalizedX * Math.PI * frequency) + phase + phaseShift).toFloat() * amplitude * edgeMute
                path.lineTo(x.toFloat(), y)
            }
            drawPath(
                path = path,
                color = Color.White.copy(alpha = 0.3f + (i * 0.1f)),
                style = Stroke(width = 4f + i)
            )
        }

        // Center Core Energy line
        drawLine(
            color = Color.White.copy(alpha = 0.8f),
            start = Offset(0f, centerY),
            end = Offset(width, centerY),
            strokeWidth = 1f
        )
    }
}

@Composable
fun BottomMicButton(appState: AppState, onClick: () -> Unit) {
    val haptic = LocalHapticFeedback.current
    val infiniteTransition = rememberInfiniteTransition()

    // Pulsating ring effect
    val rippleScale by infiniteTransition.animateFloat(
        initialValue = 1f, targetValue = 1.4f,
        animationSpec = infiniteRepeatable(tween(2000, easing = FastOutSlowInEasing), RepeatMode.Restart)
    )
    val rippleAlpha by infiniteTransition.animateFloat(
        initialValue = 1f, targetValue = 0f,
        animationSpec = infiniteRepeatable(tween(2000, easing = FastOutSlowInEasing), RepeatMode.Restart)
    )

    Column(horizontalAlignment = Alignment.CenterHorizontally) {
        Box(
            contentAlignment = Alignment.Center,
            modifier = Modifier.size(76.dp)
        ) {
            // Ripple layer
            if (appState == AppState.LISTENING || appState == AppState.IDLE) {
                Box(
                    modifier = Modifier
                        .fillMaxSize()
                        .scale(rippleScale)
                        .border(1.dp, Color(0xFF8AA3FF).copy(alpha = rippleAlpha), CircleShape)
                )
            }

            // Main Button
            Box(
                contentAlignment = Alignment.Center,
                modifier = Modifier
                    .fillMaxSize()
                    .clip(CircleShape)
                    .background(Brush.linearGradient(listOf(Color(0xFF4A65FF), Color(0xFF1E32AA))))
                    .border(2.dp, Color.White.copy(alpha = 0.1f), CircleShape)
                    .clickable {
                        haptic.performHapticFeedback(HapticFeedbackType.LongPress)
                        onClick()
                    }
                    .shadow(elevation = if (appState == AppState.LISTENING) 15.dp else 0.dp, shape = CircleShape)
            ) {
                Image(
                    painter = painterResource(id = R.drawable.mic), // Your uploaded mic icon
                    contentDescription = "Microphone",
                    modifier = Modifier.size(34.dp),
                    contentScale = ContentScale.Fit
                )
            }
        }
        Spacer(modifier = Modifier.height(14.dp))
        Text(
            text = "Tap to speak",
            color = JasicaWhite.copy(alpha = 0.85f),
            fontFamily = InterFontFamily,
            fontWeight = FontWeight.Medium,
            fontSize = 15.sp
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  WebView Action Cards (Fulfilled exact requested constraint)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * A Javascript Interface to catch clicks inside the WebView and send them to Compose natively.
 */
class WebAppInterface(private val onAction: (String) -> Unit) {
    @JavascriptInterface
    fun onAction(action: String) {
        onAction.invoke(action)
    }
}

@SuppressLint("SetJavaScriptEnabled")
@Composable
fun WebViewActionCards(onAction: (String) -> Unit) {
    // Injecting the exact HTML/CSS style generated previously into the WebView
    val htmlContent = """
        <!DOCTYPE html>
        <html>
        <head>
        <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
        <style>
            body {
                margin: 0; padding: 0;
                background: transparent;
                display: flex; gap: 8px; justify-content: center;
                font-family: 'sans-serif';
            }
            .action-card {
                flex: 1; max-width: 110px;
                background: rgba(255, 255, 255, 0.12);
                border: 1px solid rgba(255, 255, 255, 0.2);
                border-radius: 18px; padding: 12px 4px;
                display: flex; flex-direction: column; align-items: center; text-align: center;
                backdrop-filter: blur(16px); -webkit-backdrop-filter: blur(16px);
                color: white; cursor: pointer;
                box-shadow: 0 10px 30px rgba(0,0,0,0.15), inset 0 1px 1px rgba(255,255,255,0.1);
                transition: all 0.3s ease;
                -webkit-tap-highlight-color: transparent;
            }
            .action-card:active {
                background: rgba(255, 255, 255, 0.18);
                transform: translateY(2px);
            }
            .action-card svg { width: 22px; height: 22px; stroke: white; stroke-width: 1.5; fill: none; margin-bottom: 8px; }
            .action-card span { font-size: 10px; font-weight: 600; line-height: 1.4; }
        </style>
        </head>
        <body>
            <div class="action-card" onclick="AndroidBridge.onAction('Schedule Team Sync')">
                <svg viewBox="0 0 24 24"><rect x="3" y="4" width="18" height="18" rx="2" ry="2"></rect><line x1="16" y1="2" x2="16" y2="6"></line><line x1="8" y1="2" x2="8" y2="6"></line><line x1="3" y1="10" x2="21" y2="10"></line><text x="12" y="18" font-size="6" fill="white" stroke="none" text-anchor="middle" font-weight="bold">11:00</text><text x="12" y="22" font-size="3" fill="white" stroke="none" text-anchor="middle">AM</text></svg>
                <span>Schedule<br>Team Sync</span>
            </div>
            <div class="action-card" onclick="AndroidBridge.onAction('Generate Project Summary')">
                <svg viewBox="0 0 24 24"><path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"></path><polyline points="14 2 14 8 20 8"></polyline><line x1="16" y1="13" x2="8" y2="13"></line><line x1="16" y1="17" x2="8" y2="17"></line><polyline points="10 9 9 9 8 9"></polyline></svg>
                <span>Generate Project<br>Summary</span>
            </div>
            <div class="action-card" onclick="AndroidBridge.onAction('Find Presentation Slides')">
                <svg viewBox="0 0 24 24"><path d="M17.5 19H9a7 7 0 1 1 6.71-9h1.79a4.5 4.5 0 1 1 0 9Z"></path><polyline points="12 12 12 16"></polyline><polyline points="10 14 12 12 14 14"></polyline></svg>
                <span>Find Presentation<br>Slides</span>
            </div>
        </body>
        </html>
    """.trimIndent()

    AndroidView(
        modifier = Modifier.fillMaxSize(),
        factory = { context ->
            WebView(context).apply {
                // Ensure WebView background is transparent to see the Android Compose background through it
                setBackgroundColor(android.graphics.Color.TRANSPARENT)
                settings.javaScriptEnabled = true
                addJavascriptInterface(WebAppInterface(onAction), "AndroidBridge")
                loadDataWithBaseURL(null, htmlContent, "text/html", "UTF-8", null)
            }
        }
    )
}

// ─────────────────────────────────────────────────────────────────────────────
//  Dialogs (Adapted to Jasica colors)
// ─────────────────────────────────────────────────────────────────────────────

@OptIn(ExperimentalMaterial3Api::class)
@Composable
fun SettingsDialog(
    currentApiKey: String,
    currentModel: String,
    onDismiss: () -> Unit,
    onSave: (String, String) -> Unit
) {
    var apiKeyInput by remember { mutableStateOf(currentApiKey) }
    var selectedModel by remember { mutableStateOf(currentModel) }

    Dialog(onDismissRequest = onDismiss) {
        Surface(
            shape = RoundedCornerShape(24.dp),
            color = Color(0xFF1E1E24), // Darker panel for contrast
            border = BorderStroke(1.dp, JasicaPurple.copy(alpha = 0.5f)),
            modifier = Modifier.fillMaxWidth().padding(vertical = 16.dp)
        ) {
            Column(modifier = Modifier.padding(20.dp)) {
                Text(
                    text = "Jasica Settings",
                    color = JasicaOrange,
                    fontFamily = InterFontFamily,
                    fontSize = 18.sp,
                    fontWeight = FontWeight.Bold
                )

                Spacer(Modifier.height(16.dp))

                // API Key Field
                Text("API KEY", color = JasicaWhite.copy(alpha = 0.6f), fontSize = 12.sp, fontFamily = InterFontFamily)
                Spacer(Modifier.height(8.dp))
                OutlinedTextField(
                    value = apiKeyInput,
                    onValueChange = { apiKeyInput = it },
                    singleLine = true,
                    textStyle = TextStyle(color = Color.White, fontFamily = InterFontFamily, fontSize = 14.sp),
                    colors = OutlinedTextFieldDefaults.colors(
                        focusedBorderColor = JasicaPurple,
                        unfocusedBorderColor = JasicaPurple.copy(alpha = 0.3f),
                        cursorColor = JasicaOrange
                    ),
                    modifier = Modifier.fillMaxWidth()
                )

                Spacer(Modifier.height(24.dp))

                // Model Selection
                Text("AI MODEL", color = JasicaWhite.copy(alpha = 0.6f), fontSize = 12.sp, fontFamily = InterFontFamily)
                Spacer(Modifier.height(8.dp))

                AiModelsList.forEach { modelName ->
                    val isSelected = selectedModel == modelName
                    Row(
                        modifier = Modifier
                            .fillMaxWidth()
                            .padding(vertical = 4.dp)
                            .clip(RoundedCornerShape(8.dp))
                            .background(if (isSelected) JasicaPurple.copy(alpha = 0.2f) else Color.Transparent)
                            .border(1.dp, if (isSelected) JasicaPurple else Color.DarkGray, RoundedCornerShape(8.dp))
                            .clickable { selectedModel = modelName }
                            .padding(12.dp),
                        verticalAlignment = Alignment.CenterVertically
                    ) {
                        Box(modifier = Modifier.size(8.dp).clip(CircleShape).background(if (isSelected) JasicaOrange else Color.DarkGray))
                        Spacer(Modifier.width(12.dp))
                        Text(
                            text = modelName,
                            color = if (isSelected) JasicaWhite else Color.Gray,
                            fontFamily = InterFontFamily,
                            fontSize = 14.sp,
                            fontWeight = if (isSelected) FontWeight.Bold else FontWeight.Normal
                        )
                    }
                }

                Spacer(Modifier.height(24.dp))

                Row(
                    modifier = Modifier.fillMaxWidth(),
                    horizontalArrangement = Arrangement.End
                ) {
                    TextButton(onClick = onDismiss) {
                        Text("CANCEL", color = Color.Gray, fontFamily = InterFontFamily, fontSize = 14.sp)
                    }
                    Spacer(Modifier.width(8.dp))
                    TextButton(onClick = { onSave(apiKeyInput, selectedModel) }) {
                        Text("SAVE", color = JasicaOrange, fontFamily = InterFontFamily, fontSize = 14.sp, fontWeight = FontWeight.Bold)
                    }
                }
            }
        }
    }
}

@SuppressLint("MissingPermission")
@Composable
fun DeviceSelectionDialog(pairedDevices: List<BluetoothDevice>, availableDevices: List<BluetoothDevice>, isScanning: Boolean, onDeviceSelect: (BluetoothDevice) -> Unit, onScanTap: () -> Unit, onDismiss: () -> Unit) {
    Dialog(onDismissRequest = onDismiss) {
        Surface(
            shape = RoundedCornerShape(24.dp),
            color = Color(0xFF1E1E24),
            border = BorderStroke(1.dp, JasicaPurple.copy(alpha = 0.5f)),
            modifier = Modifier.fillMaxWidth().padding(vertical = 16.dp)
        ) {
            Column(modifier = Modifier.padding(20.dp)) {
                Row(modifier = Modifier.fillMaxWidth(), horizontalArrangement = Arrangement.SpaceBetween, verticalAlignment = Alignment.CenterVertically) {
                    Text("Bluetooth Devices", color = JasicaOrange, fontFamily = InterFontFamily, fontSize = 18.sp, fontWeight = FontWeight.Bold)
                    if (isScanning) {
                        CircularProgressIndicator(modifier = Modifier.size(20.dp), color = JasicaPurple, strokeWidth = 2.dp)
                    } else {
                        TextButton(onClick = onScanTap) {
                            Text("SCAN", color = JasicaPurple, fontFamily = InterFontFamily, fontSize = 14.sp, fontWeight = FontWeight.Bold)
                        }
                    }
                }

                Spacer(Modifier.height(8.dp))

                LazyColumn(modifier = Modifier.heightIn(max = 350.dp)) {
                    if (pairedDevices.isNotEmpty()) {
                        item { Text("PAIRED DEVICES", color = JasicaWhite.copy(alpha = 0.6f), fontSize = 12.sp, fontFamily = InterFontFamily, modifier = Modifier.padding(vertical = 8.dp)) }
                        items(pairedDevices) { device -> DeviceListItem(device.name ?: "Unknown Device", device.address) { onDeviceSelect(device) } }
                    }

                    item { Spacer(Modifier.height(12.dp)); Text("AVAILABLE DEVICES", color = JasicaWhite.copy(alpha = 0.6f), fontSize = 12.sp, fontFamily = InterFontFamily, modifier = Modifier.padding(vertical = 8.dp)) }

                    if (availableDevices.isEmpty() && !isScanning) {
                        item { Text("No devices found.", color = Color.Gray, fontSize = 14.sp, fontFamily = InterFontFamily, modifier = Modifier.padding(vertical = 12.dp)) }
                    } else {
                        items(availableDevices) { device -> DeviceListItem(device.name ?: "Unknown Signal", device.address) { onDeviceSelect(device) } }
                    }
                }

                Spacer(Modifier.height(16.dp))

                TextButton(onClick = onDismiss, modifier = Modifier.align(Alignment.End)) {
                    Text("CLOSE", color = Color.Gray, fontFamily = InterFontFamily, fontSize = 14.sp)
                }
            }
        }
    }
}

@Composable
fun DeviceListItem(name: String, address: String, onClick: () -> Unit) {
    Row(
        modifier = Modifier
            .fillMaxWidth()
            .padding(vertical = 6.dp)
            .clip(RoundedCornerShape(12.dp))
            .background(JasicaCardBg)
            .clickable { onClick() }
            .padding(12.dp),
        verticalAlignment = Alignment.CenterVertically
    ) {
        Icon(imageVector = Icons.Default.Bluetooth, contentDescription = null, tint = JasicaPurple)
        Spacer(Modifier.width(12.dp))
        Column {
            Text(name, color = Color.White, fontSize = 15.sp, fontFamily = InterFontFamily, fontWeight = FontWeight.SemiBold)
            Text(address, color = JasicaWhite.copy(alpha = 0.5f), fontSize = 12.sp, fontFamily = InterFontFamily)
        }
    }
}