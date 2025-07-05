import tkinter as tk
from tkinter import ttk, messagebox
import threading
import time
import random
import collections # Para usar deque en la cola FCFS

# --- ESTRUCTURAS DE DATOS ---

class Proceso:
    """Clase que representa a un proceso en la cola."""
    def __init__(self, id_proceso, tiempo_llegada, tiempo_rafaga, priority=None, queue_type=None):
        """
        Inicializa un nuevo proceso.
        Args:
            id_proceso (str): Identificador único del proceso.
            tiempo_llegada (int): Tiempo en el que el proceso llega al sistema.
            tiempo_rafaga (int): Tiempo total de CPU que el proceso necesita.
            priority (int): Prioridad del proceso (menor número = mayor prioridad) para la cola PQ.
            queue_type (str): Tipo de cola a la que pertenece ("RR", "FCFS", "PQ").
        """
        self.id = id_proceso
        self.t_llegada = tiempo_llegada  # Tiempo de llegada actual (puede cambiar al ser re-encolado/desbloqueado)
        self.bt = tiempo_rafaga  # Ráfaga restante actual

        self.original_at = tiempo_llegada  # Tiempo de llegada original al sistema
        self.original_bt = tiempo_rafaga  # Ráfaga original total que necesita el proceso

        self.siguiente = None  # Enlace al siguiente proceso en la lista circular (solo para RR)
        self.priority = priority # Añadido para la cola de Prioridades
        self.queue_type = queue_type # Añadido para identificar su cola original

        self.t_arranque = -1  # Primer momento en que el proceso entra a CPU
        self.total_executed_in_cpu = 0  # Tiempo total que el proceso ha ejecutado en CPU (acumulado)
        self.last_cpu_exit_time = -1 # Último momento en que el proceso salió de CPU (para calcular espera entre fragmentos)
        self.fragment_count = 0 # Contador para identificar los fragmentos (P1-1, P1-2, etc.)

    def __str__(self):
        """Representación en cadena del proceso."""
        return f"Proceso {self.id} (Llegada Orig: {self.original_at}, Ráfaga Orig: {self.original_bt}, Ráfaga Rest: {self.bt:.1f}, Tipo: {self.queue_type}, Prioridad: {self.priority})"


class ListaCircular:
    """
    Clase que representa la lista circular de procesos listos (cola de listos).
    El puntero 'ultimo' apunta al último proceso agregado.
    El 'siguiente' del 'ultimo' es el "primero" en la cola (cabeza).
    """
    def __init__(self):
        """Inicializa una lista circular vacía."""
        self.ultimo = None

    def esta_vacia(self):
        """Verifica si la lista está vacía."""
        return self.ultimo is None

    def encolar_proceso(self, nuevo_proceso):
        """Agrega un proceso al final de la cola circular."""
        if self.esta_vacia():
            self.ultimo = nuevo_proceso
            nuevo_proceso.siguiente = nuevo_proceso
        else:
            nuevo_proceso.siguiente = self.ultimo.siguiente
            self.ultimo.siguiente = nuevo_proceso
            self.ultimo = nuevo_proceso

    def desencolar_proceso_rr(self):
        """
        Elimina y retorna el proceso al frente de la cola (el que sigue a 'ultimo').
        Este es el comportamiento necesario para Round Robin.
        """
        if self.esta_vacia():
            return None
        proceso_a_ejecutar = self.ultimo.siguiente
        if self.ultimo == self.ultimo.siguiente:  # Caso: solo hay un elemento.
            self.ultimo = None  # La lista queda vacía.
        else:
            self.ultimo.siguiente = proceso_a_ejecutar.siguiente
        return proceso_a_ejecutar

    def obtener_procesos_en_orden(self):
        """Retorna una lista Python de los procesos en orden de atención para la UI."""
        if self.esta_vacia():
            return []
        procesos_ordenados = []
        actual = self.ultimo.siguiente
        while True:
            procesos_ordenados.append(actual)
            actual = actual.siguiente
            if actual == self.ultimo.siguiente: # Regresó al inicio
                break
        return procesos_ordenados

# --- VARIABLES GLOBALES ---
master_procesos = [] # Lista de todos los procesos agregados al sistema
cola_rr = ListaCircular() # Cola Round Robin (Prioridad 1 - Alta)
cola_fcfs = collections.deque() # Cola FCFS (Prioridad 2 - Media)
cola_pq = [] # Cola de Prioridades (Prioridad 3 - Baja) - se manejará como una lista ordenada

procesos_ejecutados_completos = [] # Lista para almacenar los resultados de procesos terminados (para calculo de promedios)
simulacion_activa = False
simulacion_pausada = False
cpu_tiempo_actual = 0.0 # Tiempo global actual de la CPU
hilo_simulacion = None # Referencia al hilo de la simulación
procesos_por_llegar = [] # Procesos que aún no han llegado o que fueron desbloqueados
cola_bloqueados = [] # Lista FIFO de procesos bloqueados
bloqueo_solicitado = False # Bandera para indicar que se ha solicitado un bloqueo
proceso_actual_en_cpu = None # Referencia al proceso que actualmente ejecuta la CPU
quantum_value = None # Valor del quantum para Round Robin

# Niveles de prioridad de las colas (menor número = mayor prioridad)
QUEUE_PRIORITIES = {
    "RR": 1,
    "FCFS": 2,
    "PQ": 3
}

# Variables para el Gantt y tabla de fragmentos
procesos_por_llegar_lock = threading.Lock() # Bloqueo para acceder a procesos_por_llegar de forma segura entre hilos
next_gantt_y_offset = 0 # Desplazamiento Y para la siguiente fila en el Gantt
gantt_process_y_mapping = {} # Mapeo de ID de proceso a su offset Y en el Gantt
fragmentos_ejecucion = [] # Almacena datos de cada segmento de ejecución para el Gantt y la tabla de resultados detallada

COLORES_PROCESOS = ["#FF6347", "#6A5ACD", "#3CB371", "#FFD700", "#BA55D3", "#4682B4", "#DAA520", "#DC143C", "#20B2AA", "#7B68EE"]
random.shuffle(COLORES_PROCESOS) # Aleatorizar colores

# --- FUNCIONES DE LÓGICA DE SIMULACIÓN ---

def ejecutar_simulacion():
    """
    Función principal de la simulación Multi-Cola.
    Gestiona la llegada de procesos, ejecución, preempción, bloqueo y finalización
    a través de las colas RR, FCFS y PQ.
    """
    global cpu_tiempo_actual, simulacion_activa, simulacion_pausada
    global procesos_ejecutados_completos, cola_rr, cola_fcfs, cola_pq, procesos_por_llegar
    global gantt_process_y_mapping, next_gantt_y_offset
    global proceso_actual_en_cpu, bloqueo_solicitado, quantum_value, cola_bloqueados, fragmentos_ejecucion

    idx_color = 0 # Índice para ciclar los colores del Gantt

    # La simulación continúa mientras haya procesos en cualquier estado (por llegar, listos, ejecutando, bloqueados)
    while (procesos_por_llegar or not cola_rr.esta_vacia() or cola_fcfs or cola_pq or proceso_actual_en_cpu or cola_bloqueados) and simulacion_activa:
        # Pausa la simulación si está solicitada
        while simulacion_pausada and simulacion_activa:
            time.sleep(0.1)
            root.update_idletasks() # Permite que la UI se actualice mientras está en pausa
        if not simulacion_activa: # Si la simulación fue detenida durante la pausa
            break

        # 1. Procesar llegadas y desbloqueos: Mover procesos a la cola de listos correspondiente
        with procesos_por_llegar_lock:
            # Iterar sobre una copia para poder modificar la lista original
            for p_arrival in list(procesos_por_llegar):
                if p_arrival.t_llegada <= cpu_tiempo_actual:
                    if p_arrival.queue_type == "RR":
                        cola_rr.encolar_proceso(p_arrival)
                    elif p_arrival.queue_type == "FCFS":
                        cola_fcfs.append(p_arrival)
                    elif p_arrival.queue_type == "PQ":
                        cola_pq.append(p_arrival)
                        cola_pq.sort(key=lambda p: p.priority) # Mantener la cola PQ ordenada por prioridad
                    procesos_por_llegar.remove(p_arrival)
                    update_console(f"[Sistema] Proceso {p_arrival.id} ({p_arrival.queue_type}) llegó o fue desbloqueado y va a Listos (AT: {p_arrival.t_llegada:.1f})", "sistema_nuevo_proceso")
            procesos_por_llegar.sort(key=lambda p: p.t_llegada) # Mantener la lista ordenada por tiempo de llegada

        actualizar_vista_cola_procesos() # Actualiza la UI de las colas
        actualizar_tabla_rr_queue() # Actualizar la tabla de la cola RR
        actualizar_tabla_fcfs_queue() # Actualizar la tabla de la cola FCFS
        actualizar_tabla_pq_queue() # Actualizar la tabla de la cola PQ

        # 2. Preempción por llegada de proceso de mayor prioridad (si hay un proceso ejecutándose)
        # Esta lógica verifica si un proceso actualmente en la CPU debe ser preempted
        # porque un proceso de mayor prioridad ha llegado a una cola de mayor prioridad.
        if proceso_actual_en_cpu:
            current_queue_priority = QUEUE_PRIORITIES[proceso_actual_en_cpu.queue_type]
            # Verificar si alguna cola de mayor prioridad tiene procesos listos
            # Condición 1: Hay procesos en RR y el proceso actual no es RR (RR es la más alta prioridad)
            # Condición 2: Hay procesos en FCFS y el proceso actual no es FCFS ni RR (FCFS es media prioridad)
            # Condición 3: Hay procesos en PQ y el proceso actual no es PQ, RR o FCFS,
            #              O si es de PQ y llega uno de mayor prioridad a PQ (preempción dentro de PQ por prioridad)
            if (not cola_rr.esta_vacia() and current_queue_priority > QUEUE_PRIORITIES["RR"]) or \
               (cola_fcfs and current_queue_priority > QUEUE_PRIORITIES["FCFS"]) or \
               (cola_pq and current_queue_priority > QUEUE_PRIORITIES["PQ"] and cola_pq[0].priority < proceso_actual_en_cpu.priority):
                
                # Preempt the currently running process
                p = proceso_actual_en_cpu
                update_console(f"[CPU] {p.id} ({p.queue_type}) preempted by higher priority arrival. Re-enqueuing...", "sistema_advertencia")
                
                # Re-encolar el proceso preempted a su cola original
                p.t_llegada = cpu_tiempo_actual # Su "nueva" llegada es el momento actual de la CPU
                if p.queue_type == "RR":
                    cola_rr.encolar_proceso(p)
                elif p.queue_type == "FCFS":
                    cola_fcfs.appendleft(p) # Para FCFS, se re-inserta al frente para mantener el orden
                elif p.queue_type == "PQ":
                    cola_pq.append(p)
                    cola_pq.sort(key=lambda proc: proc.priority) # Re-ordenar la cola PQ para mantener la prioridad
                
                proceso_actual_en_cpu = None # La CPU queda libre para el siguiente ciclo
                actualizar_vista_cola_procesos()
                actualizar_tabla_rr_queue()
                actualizar_tabla_fcfs_queue()
                actualizar_tabla_pq_queue()
                continue # Volver a la siguiente iteración principal para seleccionar el proceso de mayor prioridad

        # 3. Seleccionar el siguiente proceso a ejecutar según la prioridad de las colas
        proceso_a_ejecutar = None
        if not cola_rr.esta_vacia():
            proceso_a_ejecutar = cola_rr.desencolar_proceso_rr()
        elif cola_fcfs:
            proceso_a_ejecutar = cola_fcfs.popleft()
        elif cola_pq:
            cola_pq.sort(key=lambda p: p.priority) # Asegurar que esté ordenada antes de sacar el de mayor prioridad
            proceso_a_ejecutar = cola_pq.pop(0)

        if proceso_a_ejecutar:
            p = proceso_a_ejecutar
            proceso_actual_en_cpu = p

            # Calcular el tiempo de espera antes de este fragmento
            t_espera = max(0.0, cpu_tiempo_actual - p.t_llegada)

            # Registrar el primer momento en que el proceso entra a CPU
            if p.t_arranque == -1:
                p.t_arranque = cpu_tiempo_actual
            
            # Determinar el tiempo de ejecución para este "slice"
            run_time_for_slice = p.bt # Por defecto, ejecuta toda la ráfaga (para FCFS y PQ)
            if p.queue_type == "RR":
                run_time_for_slice = min(p.bt, quantum_value) # Para RR, respeta el quantum
            
            start_of_current_execution = cpu_tiempo_actual # Tiempo de inicio para dibujar este fragmento
            
            update_console(f"[CPU] {p.id} ({p.queue_type}) ejecuta {run_time_for_slice:.1f}u (restante: {p.bt-run_time_for_slice:.1f}u)", "ejecucion")

            ejecutado_rafaga_actual = 0.0
            # Simular la ejecución en pequeños pasos (0.1s)
            # Continúa mientras queden unidades de tiempo en el slice, la simulación esté activa y no haya solicitud de bloqueo
            while ejecutado_rafaga_actual < run_time_for_slice - 1e-9 and simulacion_activa and not bloqueo_solicitado:
                # Manejar pausas durante la ejecución del slice
                while simulacion_pausada and simulacion_activa:
                    time.sleep(0.1)
                    root.update_idletasks()
                if not simulacion_activa: # Si la simulación fue detenida durante la pausa
                    break

                # Verificar preempción por llegada de mayor prioridad *durante* la ejecución del slice
                # Esta es una verificación continua para preempción si un proceso de mayor prioridad
                # llega mientras otro de menor prioridad está ejecutándose.
                with procesos_por_llegar_lock:
                    for p_arrival_check in list(procesos_por_llegar):
                        if p_arrival_check.t_llegada <= cpu_tiempo_actual:
                            # Mover a la cola correspondiente
                            if p_arrival_check.queue_type == "RR":
                                cola_rr.encolar_proceso(p_arrival_check)
                            elif p_arrival_check.queue_type == "FCFS":
                                cola_fcfs.append(p_arrival_check)
                            elif p_arrival_check.queue_type == "PQ":
                                cola_pq.append(p_arrival_check)
                                cola_pq.sort(key=lambda pc: pc.priority)
                            procesos_por_llegar.remove(p_arrival_check)
                            update_console(f"[Sistema] Proceso {p_arrival_check.id} ({p_arrival_check.queue_type}) llegó y va a Listos (AT: {p_arrival_check.t_llegada:.1f})", "sistema_nuevo_proceso")
                    procesos_por_llegar.sort(key=lambda p: p.t_llegada) # Reordenar por tiempo de llegada

                current_queue_priority = QUEUE_PRIORITIES[p.queue_type]
                if (not cola_rr.esta_vacia() and current_queue_priority > QUEUE_PRIORITIES["RR"]) or \
                   (cola_fcfs and current_queue_priority > QUEUE_PRIORITIES["FCFS"]) or \
                   (cola_pq and current_queue_priority > QUEUE_PRIORITIES["PQ"] and cola_pq[0].priority < p.priority):
                    
                    update_console(f"[CPU] {p.id} ({p.queue_type}) preempted by higher priority arrival DURING execution. Re-enqueuing...", "sistema_advertencia")
                    
                    # Guardar el estado del fragmento ejecutado hasta ahora
                    p.bt -= ejecutado_rafaga_actual # Actualizar ráfaga restante
                    p.total_executed_in_cpu += ejecutado_rafaga_actual
                    p.last_cpu_exit_time = cpu_tiempo_actual
                    
                    p.fragment_count += 1
                    fragment_id = f"{p.id}-{p.fragment_count}"
                    fragment_info = {
                        'fragment_id': fragment_id,
                        'original_id': p.id,
                        't_llegada': p.original_at,
                        'bt': p.original_bt,
                        'start_time': start_of_current_execution,
                        't_final': cpu_tiempo_actual,
                        'duration': ejecutado_rafaga_actual,
                        'wait_time_before_fragment': t_espera,
                        'is_completed': False,
                        'queue_type': p.queue_type
                    }
                    fragmentos_ejecucion.append(fragment_info)
                    dibujar_proceso_en_gantt(fragment_info, COLORES_PROCESOS[idx_color % len(COLORES_PROCESOS)])
                    actualizar_tabla_resultados(fragmentos_ejecucion)
                    actualizar_tabla_rr_queue()
                    actualizar_tabla_fcfs_queue()
                    actualizar_tabla_pq_queue()

                    # Re-encolar el proceso preempted
                    p.t_llegada = cpu_tiempo_actual # Su "nueva" llegada es el momento actual de la CPU
                    if p.queue_type == "RR":
                        cola_rr.encolar_proceso(p)
                    elif p.queue_type == "FCFS":
                        cola_fcfs.appendleft(p) # Se re-inserta al frente
                    elif p.queue_type == "PQ":
                        cola_pq.append(p)
                        cola_pq.sort(key=lambda proc: proc.priority)
                    
                    proceso_actual_en_cpu = None
                    actualizar_vista_cola_procesos()
                    break # Salir del bucle interno, se seleccionará el nuevo proceso de mayor prioridad en el bucle externo

                step = min(0.1, run_time_for_slice - ejecutado_rafaga_actual) # Tomar el paso de tiempo, sin exceder el slice
                
                time.sleep(step) # Simular el paso de tiempo
                cpu_tiempo_actual += step
                ejecutado_rafaga_actual += step
                
                dibujar_linea_tiempo_gantt(cpu_tiempo_actual)
            
            # Después del bucle interno (slice finalizado, simulación detenida, bloqueo o preempción)
            if not simulacion_activa:
                break # Detener toda la simulación

            # Si el proceso fue preempted DURANTE el slice por llegada de mayor prioridad,
            # ya se manejó el re-encolamiento y el registro del fragmento dentro del bucle interno.
            # Así que, verificar si 'proceso_actual_en_cpu' sigue siendo el mismo 'p'.
            if proceso_actual_en_cpu != p: # Significa que fue preempted y reemplazado
                continue # Ir a la siguiente iteración principal del bucle para seleccionar el nuevo proceso actual

            # Si llega aquí, el slice se completó de forma natural o debido a un bloqueo
            p.bt -= ejecutado_rafaga_actual
            p.total_executed_in_cpu += ejecutado_rafaga_actual
            p.last_cpu_exit_time = cpu_tiempo_actual

            # Preparar datos del fragmento
            p.fragment_count += 1
            fragment_id = f"{p.id}-{p.fragment_count}"
            
            fragment_info = {
                'fragment_id': fragment_id,
                'original_id': p.id,
                't_llegada': p.original_at, # Usar AT original del proceso completo
                'bt': p.original_bt, # Usar BT original del proceso completo
                'start_time': start_of_current_execution,
                't_final': cpu_tiempo_actual,
                'duration': ejecutado_rafaga_actual,
                'wait_time_before_fragment': t_espera, # Tiempo de espera antes de este fragmento
                'is_completed': False, # Indica si este fragmento es el que finaliza el proceso
                'queue_type': p.queue_type # Añadir el tipo de cola al fragmento
            }

            if bloqueo_solicitado:
                fragmentos_ejecucion.append(fragment_info)
                dibujar_proceso_en_gantt(fragment_info, COLORES_PROCESOS[idx_color % len(COLORES_PROCESOS)])
                actualizar_tabla_resultados(fragmentos_ejecucion) # Actualizar tabla con el nuevo fragmento
                actualizar_tabla_rr_queue()
                actualizar_tabla_fcfs_queue()
                actualizar_tabla_pq_queue()

                if p.bt > 0:
                    # Crear una copia del proceso para poner en la cola de bloqueados
                    blocked_p = Proceso(p.id, cpu_tiempo_actual, p.bt, p.priority, p.queue_type)
                    blocked_p.original_at = p.original_at
                    blocked_p.original_bt = p.original_bt
                    blocked_p.t_arranque = p.t_arranque
                    blocked_p.total_executed_in_cpu = p.total_executed_in_cpu
                    blocked_p.last_cpu_exit_time = p.last_cpu_exit_time
                    blocked_p.fragment_count = p.fragment_count # Mantener el contador de fragmentos
                    cola_bloqueados.append(blocked_p)
                    update_console(f"[CPU] {p.id} ({p.queue_type}) BLOQUEADO (restan {p.bt:.1f}u).", "sistema_advertencia")
                else: # El proceso terminó justo antes o al momento del bloqueo
                    fragment_info['is_completed'] = True # Marcar este fragmento como final
                    t_final = cpu_tiempo_actual
                    turnaround = t_final - p.original_at
                    waiting = turnaround - p.original_bt

                    procesos_ejecutados_completos.append({
                        'id': p.id, 't_llegada': p.original_at, 'bt': p.original_bt,
                        'start_time': p.t_arranque, 't_final': t_final,
                        't_espera': turnaround, 'waiting_time': waiting
                    })
                    update_console(f"[CPU] {p.id} ({p.queue_type}) TERMINÓ en t={t_final:.1f}", "terminado")
                
                bloqueo_solicitado = False
                proceso_actual_en_cpu = None
                continue # Ir a la siguiente iteración principal del bucle

            # Si el slice se completó de forma natural (no bloqueado, no detenido, no preemted por mayor prioridad)
            fragmentos_ejecucion.append(fragment_info)
            dibujar_proceso_en_gantt(fragment_info, COLORES_PROCESOS[idx_color % len(COLORES_PROCESOS)])
            actualizar_tabla_resultados(fragmentos_ejecucion) # Actualizar tabla con el nuevo fragmento
            actualizar_tabla_rr_queue()
            actualizar_tabla_fcfs_queue()
            actualizar_tabla_pq_queue()

            if p.bt <= 1e-9: # Proceso terminado
                p.bt = 0.0
                fragment_info['is_completed'] = True # Marcar este fragmento como final
                t_final = cpu_tiempo_actual
                turnaround = t_final - p.original_at
                waiting = turnaround - p.original_bt

                procesos_ejecutados_completos.append({
                    'id': p.id, 't_llegada': p.original_at, 'bt': p.original_bt,
                    'start_time': p.t_arranque, 't_final': t_final,
                    't_espera': turnaround, 'waiting_time': waiting
                })
                update_console(f"[CPU] {p.id} ({p.queue_type}) TERMINÓ en t={t_final:.1f}", "terminado")
                idx_color += 1
                proceso_actual_en_cpu = None
            else: # Proceso no terminado, re-encolar según su tipo de cola
                # Si es RR, se reencola. Si es FCFS o PQ, solo debería llegar aquí si fue preempted por quantum (lo cual no ocurre)
                # o por un proceso de mayor prioridad que llegó justo al final de su slice.
                # En este caso, simplemente lo re-encolamos a su cola original.
                update_console(f"[CPU] {p.id} ({p.queue_type}) fue PREEMPTADO y reencolado (restan {p.bt:.1f}u).", "sistema_advertencia")
                p.t_llegada = cpu_tiempo_actual # Su "nueva" llegada es el momento actual de la CPU
                if p.queue_type == "RR":
                    cola_rr.encolar_proceso(p)
                elif p.queue_type == "FCFS":
                    cola_fcfs.append(p) # Añadir al final de FCFS
                elif p.queue_type == "PQ":
                    cola_pq.append(p)
                    cola_pq.sort(key=lambda proc: proc.priority) # Re-ordenar la cola PQ
                proceso_actual_en_cpu = None
            
        # 4. CPU ociosa: Si no hay procesos listos en ninguna cola, adelantar el tiempo hasta el siguiente evento
        else:
            with procesos_por_llegar_lock:
                next_event_time = float('inf')
                # Determinar el tiempo de llegada más temprano del próximo proceso por llegar
                if procesos_por_llegar:
                    next_event_time = procesos_por_llegar[0].t_llegada
                
                # Si no hay procesos por llegar pero hay bloqueados, la CPU está ociosa esperando un desbloqueo manual
                if not procesos_por_llegar and cola_bloqueados and cola_rr.esta_vacia() and not cola_fcfs and not cola_pq:
                    update_console("[CPU] Ocioso. Esperando procesos bloqueados para ser desbloqueados o nuevos procesos.", "sistema_advertencia")
                    time.sleep(0.1) # Evitar un bucle de espera ocupada
                    cpu_tiempo_actual += 0.1
                    dibujar_linea_tiempo_gantt(cpu_tiempo_actual)
                    continue # Volver a verificar colas

                # Adelantar el tiempo si la CPU está ociosa hasta la próxima llegada
                if next_event_time != float('inf'): # Si hay un próximo evento
                    while cpu_tiempo_actual < next_event_time - 1e-9 and simulacion_activa: # Usar epsilon para flotantes
                        time.sleep(0.05) # Pequeños incrementos de tiempo ocioso
                        cpu_tiempo_actual += 0.1
                        dibujar_linea_tiempo_gantt(cpu_tiempo_actual)
                else: # No hay más procesos pendientes, listos o bloqueados en ninguna cola
                    break

    # Fin de la simulación
    if simulacion_activa:
        update_console("[Sistema] Simulación Multi-Cola completada.", "sistema")
    else:
        update_console("[Sistema] Simulación detenida.", "sistema_advertencia")

    # Actualizar promedios de los procesos completos al finalizar
    total_tat, total_wt = 0.0, 0.0
    if procesos_ejecutados_completos:
        for proc in procesos_ejecutados_completos:
            total_tat += proc['t_espera']
            total_wt += proc['waiting_time']
        avg_tat, avg_wt = total_tat / len(procesos_ejecutados_completos), total_wt / len(procesos_ejecutados_completos)
        label_promedios.config(text=f"Promedio TAT (Proceso Completo): {avg_tat:.2f} | Promedio WT (Proceso Completo): {avg_wt:.2f}")
    else:
        label_promedios.config(text="Promedio TAT (Proceso Completo): N/A | Promedio WT (Proceso Completo): N/A")

    desactivar_controles_simulacion() # Desactiva los botones de control al finalizar
    btn_iniciar.config(state=tk.NORMAL) # Habilitar iniciar de nuevo
    entry_quantum.config(state=tk.NORMAL) # Habilitar edición del quantum

# --- FUNCIONES DE INTERFAZ GRÁFICA (UI) ---

def update_console(msg, tag="normal"):
    """Inserta un mensaje en la consola de la UI."""
    consola_text.config(state='normal')
    consola_text.insert(tk.END, msg + "\n", tag)
    consola_text.see(tk.END) # Scroll automático al final
    consola_text.config(state='disabled')

def dibujar_linea_tiempo_gantt(tiempo_actual=0):
    """Dibuja la línea de tiempo y las marcas en el gráfico de Gantt."""
    PX_POR_UNIDAD_TIEMPO = 20 # Píxeles por unidad de tiempo
    canvas_gantt.delete("linea_tiempo", "eje_tiempo") # Borrar líneas y marcas anteriores

    # Línea base del eje de tiempo
    canvas_gantt.create_line(0, 50, 2000, 50, fill="black", width=2, tags="eje_tiempo")

    # Calcular el tiempo máximo para mostrar en el Gantt (un poco más allá del tiempo actual o procesos finalizados)
    max_time_gantt = max(20, tiempo_actual + 5)
    if procesos_ejecutados_completos:
        max_time_gantt = max(max_time_gantt, max(res['t_final'] for res in procesos_ejecutados_completos) + 5)
    with procesos_por_llegar_lock:
        if procesos_por_llegar:
            # Considerar el tiempo de llegada + ráfaga original de los procesos por llegar para el tamaño del Gantt
            max_time_gantt = max(max_time_gantt, max(p.original_at + p.original_bt for p in procesos_por_llegar) + 5)

    # Dibujar marcas de tiempo y etiquetas
    for t in range(0, int(max_time_gantt) + 2):
        x = t * PX_POR_UNIDAD_TIEMPO
        canvas_gantt.create_line(x, 45, x, 55, fill="gray", tags="eje_tiempo")
        canvas_gantt.create_text(x, 35, text=str(t), fill="black", font=("Arial", 8, "bold"), tags="eje_tiempo")

    # Línea roja vertical que indica el tiempo actual de la simulación
    x_actual = tiempo_actual * PX_POR_UNIDAD_TIEMPO
    canvas_gantt.create_line(x_actual, 0, x_actual, canvas_gantt.winfo_height(), fill="red", width=2, tags="linea_tiempo")
    canvas_gantt.create_text(x_actual + 5, 10, text=f"{tiempo_actual:.1f}s", fill="red", font=("Arial", 8, "bold"), anchor="w", tags="linea_tiempo")

    # Ajustar la región de scroll del canvas
    canvas_gantt.configure(scrollregion=canvas_gantt.bbox("all"))

def dibujar_proceso_en_gantt(slice_data, color):
    """Dibuja un fragmento de ejecución de un proceso en el gráfico de Gantt."""
    global next_gantt_y_offset, gantt_process_y_mapping
    PX_POR_UNIDAD_TIEMPO, ROW_HEIGHT, BAR_HEIGHT, START_Y_GANTT = 20, 45, 25, 70
    process_original_id = slice_data['original_id'] # Usar el ID original del proceso para mapeo de fila
    
    # Asignar una fila única en el Gantt para cada proceso original
    if process_original_id not in gantt_process_y_mapping:
        gantt_process_y_mapping[process_original_id] = next_gantt_y_offset
        # Añadir la etiqueta del proceso a la izquierda del Gantt
        canvas_gantt.create_text(5, START_Y_GANTT + next_gantt_y_offset * ROW_HEIGHT + BAR_HEIGHT / 2,
                                 text=f"P{process_original_id}", fill="blue", font=("Arial", 9, "bold"), anchor="w",
                                 tags=f"gantt_label_{process_original_id}")
        next_gantt_y_offset += 1

    y_base = START_Y_GANTT + gantt_process_y_mapping[process_original_id] * ROW_HEIGHT
    x_inicio = slice_data['start_time'] * PX_POR_UNIDAD_TIEMPO
    x_fin = slice_data['t_final'] * PX_POR_UNIDAD_TIEMPO

    # Ajustar la altura del canvas si es necesario para acomodar nuevas filas
    required_height = y_base + BAR_HEIGHT + 50
    if canvas_gantt.winfo_height() < required_height:
        canvas_gantt.config(height=required_height)

    # --- Dibujar línea discontinua de espera (solo si es el primer fragmento y hubo espera) ---
    if slice_data['start_time'] > slice_data['t_llegada'] + 1e-9 and slice_data['fragment_id'].endswith("-1"):
        x_llegada_original = slice_data['t_llegada'] * PX_POR_UNIDAD_TIEMPO
        canvas_gantt.create_line(x_llegada_original, y_base + BAR_HEIGHT / 2,
                                 x_inicio, y_base + BAR_HEIGHT / 2,
                                 fill="deepskyblue", width=3, dash=(4, 2))
    elif slice_data['wait_time_before_fragment'] > 1e-9: # Si hubo espera entre fragmentos
        canvas_gantt.create_line(x_inicio - slice_data['wait_time_before_fragment'] * PX_POR_UNIDAD_TIEMPO, y_base + BAR_HEIGHT / 2,
                                 x_inicio, y_base + BAR_HEIGHT / 2,
                                 fill="deepskyblue", width=3, dash=(4, 2))

    # Dibujar la barra de ejecución del fragmento
    canvas_gantt.create_rectangle(x_inicio, y_base, x_fin, y_base + BAR_HEIGHT, fill=color, outline="black")
    # Dibujar el ID del fragmento dentro de la barra
    canvas_gantt.create_text((x_inicio + x_fin) / 2, y_base + BAR_HEIGHT / 2, text=slice_data['fragment_id'], fill="black", font=("Arial", 9, "bold"))
    
    # Ajustar la región de scroll después de dibujar
    canvas_gantt.configure(scrollregion=canvas_gantt.bbox("all"))

def actualizar_vista_cola_procesos():
    """Actualiza el panel que muestra el estado de los procesos: listos, pendientes y bloqueados."""
    # Limpiar los widgets existentes en el frame
    for widget in frame_cola_listos.winfo_children():
        widget.destroy()

    # --- Procesos en Cola Round Robin (RR) ---
    listos_rr = cola_rr.obtener_procesos_en_orden()
    if listos_rr:
        tk.Label(frame_cola_listos, text="Cola RR (Prioridad 1):", bg="lightgray", fg="black", font=("Arial", 10, "bold")).pack(anchor="w", padx=5)
        for proc in listos_rr:
            tk.Label(frame_cola_listos, text=f"{proc.id} (L:{proc.t_llegada:.1f} R:{proc.bt:.1f})", bg="white", fg="black", font=("Arial", 9), relief="solid", bd=1).pack(pady=2, padx=5, fill="x")

    # --- Procesos en Cola FCFS (Prioridad 2) ---
    if cola_fcfs:
        tk.Label(frame_cola_listos, text="Cola FCFS (Prioridad 2):", bg="lightgray", fg="black", font=("Arial", 10, "bold")).pack(anchor="w", padx=5, pady=(10, 0))
        for proc in cola_fcfs:
            tk.Label(frame_cola_listos, text=f"{proc.id} (L:{proc.t_llegada:.1f} R:{proc.bt:.1f})", bg="lightgreen", fg="black", font=("Arial", 9), relief="solid", bd=1).pack(pady=2, padx=5, fill="x")

    # --- Procesos en Cola de Prioridades (PQ) ---
    if cola_pq:
        tk.Label(frame_cola_listos, text="Cola PQ (Prioridad 3):", bg="lightgray", fg="black", font=("Arial", 10, "bold")).pack(anchor="w", padx=5, pady=(10, 0))
        # Mostrar ordenado por prioridad
        for proc in sorted(cola_pq, key=lambda p: p.priority):
            tk.Label(frame_cola_listos, text=f"{proc.id} (L:{proc.t_llegada:.1f} R:{proc.bt:.1f} Pri:{proc.priority})", bg="lightyellow", fg="black", font=("Arial", 9), relief="solid", bd=1).pack(pady=2, padx=5, fill="x")

    # --- Procesos pendientes por llegar ---
    with procesos_por_llegar_lock:
        pendientes = sorted(procesos_por_llegar, key=lambda p: p.t_llegada)
    if pendientes:
        tk.Label(frame_cola_listos, text="Esperando Llegada/Desbloqueo:", bg="lightgray", fg="black", font=("Arial", 10, "bold")).pack(anchor="w", padx=5, pady=(10, 0))
        for proc in pendientes:
            tk.Label(frame_cola_listos, text=f"{proc.id} ({proc.queue_type}, L:{proc.t_llegada:.1f} R:{proc.bt:.1f})", bg="lightblue", fg="black", font=("Arial", 9)).pack(pady=2, padx=5, fill="x")

    # --- Procesos bloqueados ---
    if cola_bloqueados:
        tk.Label(frame_cola_listos, text="Bloqueados:", bg="lightgray", fg="black", font=("Arial", 10, "bold")).pack(anchor="w", padx=5, pady=(10, 0))
        for proc in cola_bloqueados:
            tk.Label(frame_cola_listos, text=f"{proc.id} ({proc.queue_type}, L:{proc.t_llegada:.1f}, R:{proc.bt:.1f})", bg="#FFB6C1", fg="black", font=("Arial", 9), relief="solid", bd=1).pack(pady=2, padx=5, fill="x")

    # --- Mensaje si no hay procesos ---
    if not listos_rr and not cola_fcfs and not cola_pq and not pendientes and not cola_bloqueados:
        tk.Label(frame_cola_listos, text="No hay procesos en el sistema", bg="lightgray", fg="black", font=("Arial", 10)).pack(pady=5, padx=5)
    

def actualizar_tabla_resultados(fragmentos):
    """
    Actualiza la tabla de resultados para mostrar cada fragmento de ejecución,
    incluyendo el tipo de cola.
    """
    for item in tree_resultados.get_children():
        tree_resultados.delete(item)  # Limpiar tabla

    rafaga_restante_por_proceso = {}

    for frag in fragmentos:
        original_id = frag['original_id']
        # Inicializar con la ráfaga original si es el primer fragmento
        if original_id not in rafaga_restante_por_proceso:
            rafaga_restante_por_proceso[original_id] = frag['bt']

        rafaga_antes = rafaga_restante_por_proceso[original_id]
        rafaga_despues = max(0.0, rafaga_antes - frag['duration'])
        rafaga_restante_por_proceso[original_id] = rafaga_despues

        display_id = frag['fragment_id']  # Px-y
        t_retorno = frag['t_final'] - frag['t_llegada']
        t_espera = t_retorno - frag['duration']

        # Mostrar la ráfaga original en el primer fragmento, luego la restante
        if display_id.endswith("-1"):
            bt_mostrar = f"{frag['bt']:.1f}"
        else:
            bt_mostrar = f"{rafaga_antes:.1f}"

        tree_resultados.insert(
            "", "end",
            values=(
                display_id,
                frag['t_llegada'],
                bt_mostrar,
                frag['queue_type'], # Nueva columna para el tipo de cola
                f"{frag['start_time']:.1f}",
                f"{frag['t_final']:.1f}",
                f"{t_retorno:.1f}",
                f"{t_espera:.1f}"
            )
        )

    # Promedios (igual que antes)
    if not simulacion_activa and procesos_ejecutados_completos:
        total_tat, total_wt = 0.0, 0.0
        for proc in procesos_ejecutados_completos:
            total_tat += proc['t_espera']
            total_wt += proc['waiting_time']
        avg_tat, avg_wt = total_tat / len(procesos_ejecutados_completos), total_wt / len(procesos_ejecutados_completos)
        label_promedios.config(text=f"Promedio TAT (Proceso Completo): {avg_tat:.2f} | Promedio WT (Proceso Completo): {avg_wt:.2f}")
    else:
        label_promedios.config(text="Promedio TAT (Proceso Completo): N/A | Promedio WT (Proceso Completo): N/A")


def actualizar_tabla_rr_queue():
    """Actualiza la tabla que muestra los procesos en la cola Round Robin."""
    for item in tree_rr_queue.get_children():
        tree_rr_queue.delete(item)
    
    listos_rr = cola_rr.obtener_procesos_en_orden()
    for proc in listos_rr:
        tree_rr_queue.insert("", "end", values=(
            proc.id,
            proc.t_llegada,
            f"{proc.bt:.1f}",
            quantum_value # Mostrar el quantum actual de la simulación
        ))

def actualizar_tabla_fcfs_queue():
    """Actualiza la tabla que muestra los procesos en la cola FCFS."""
    for item in tree_fcfs_queue.get_children():
        tree_fcfs_queue.delete(item)
    
    for proc in cola_fcfs:
        tree_fcfs_queue.insert("", "end", values=(
            proc.id,
            proc.t_llegada,
            f"{proc.bt:.1f}"
        ))

def actualizar_tabla_pq_queue():
    """Actualiza la tabla que muestra los procesos en la cola de Prioridades."""
    for item in tree_pq_queue.get_children():
        tree_pq_queue.delete(item)
    
    # Asegurarse de que la cola PQ esté ordenada por prioridad para la visualización
    for proc in sorted(cola_pq, key=lambda p: p.priority):
        tree_pq_queue.insert("", "end", values=(
            proc.id,
            proc.t_llegada,
            f"{proc.bt:.1f}",
            proc.priority
        ))

def agregar_proceso():
    """Añade un nuevo proceso al sistema desde la UI, asignándolo aleatoriamente o por selección a una cola."""
    pid, at_str, bt_str = entry_pid.get().strip(), entry_at.get().strip(), entry_bt.get().strip()
    queue_type_selection = combo_queue_type.get() # Obtener la selección del Combobox

    if not pid or not at_str or not bt_str:
        messagebox.showerror("Error de Entrada", "Todos los campos (ID, Llegada, Ráfaga) son obligatorios.")
        return
    try:
        t_llegada, bt = int(at_str), float(bt_str) # La ráfaga puede ser flotante
        if t_llegada < 0 or bt <= 0: raise ValueError("Tiempos deben ser positivos.")
    except ValueError:
        messagebox.showerror("Error de Entrada", "Tiempos de llegada (entero >=0) y ráfaga (número >0) deben ser válidos.")
        return
    
    # Validar que el ID de proceso sea único
    if any(p.id == pid for p in master_procesos):
        messagebox.showerror("Error de Entrada", f"El ID de proceso '{pid}' ya existe. Por favor, use uno diferente.")
        return

    # Asignar la cola basada en la selección del usuario o aleatoriamente
    assigned_queue_type = None
    if queue_type_selection == "Aleatorio":
        queue_choices = ["RR", "FCFS", "PQ"]
        assigned_queue_type = random.choice(queue_choices)
    else:
        assigned_queue_type = queue_type_selection

    assigned_priority = None
    if assigned_queue_type == "PQ":
    #assigned_priority = random.randint(1, 10) Ejemplo: prioridad aleatoria del 1 al 10 (1 es la más alta para PQ)
        try:
            assigned_priority = int(entry_priority_pq.get())
        except ValueError:
            messagebox.showerror("Error de Entrada", "Debe ingresar una prioridad válida para PQ.")
            return
    nuevo_proceso = Proceso(id_proceso=pid, tiempo_llegada=t_llegada, tiempo_rafaga=bt,
                            priority=assigned_priority, queue_type=assigned_queue_type)
    
    master_procesos.append(nuevo_proceso)
    
    with procesos_por_llegar_lock:
        procesos_por_llegar.append(nuevo_proceso)
        procesos_por_llegar.sort(key=lambda p: p.t_llegada) # Mantener la lista ordenada por tiempo de llegada
    
    update_console(f"[Sistema] Proceso {pid} registrado para cola {assigned_queue_type} (Prioridad: {assigned_priority if assigned_priority else 'N/A'}). Esperando su tiempo de llegada ({t_llegada:.1f}).", "sistema")
    actualizar_vista_cola_procesos()
    actualizar_tabla_rr_queue()
    actualizar_tabla_fcfs_queue()
    actualizar_tabla_pq_queue()
    # Limpiar campos de entrada
    entry_pid.delete(0, tk.END); entry_at.delete(0, tk.END); entry_bt.delete(0, tk.END)
    
    if not simulacion_activa and master_procesos:
        btn_iniciar.config(state=tk.NORMAL) # Habilitar el botón de iniciar si hay procesos

def bloquear_proceso_actual():
    """Solicita el bloqueo del proceso actualmente en la CPU."""
    global bloqueo_solicitado
    if proceso_actual_en_cpu is None:
        messagebox.showinfo("Sin proceso", "No hay proceso ejecutándose para bloquear. La CPU está ociosa o pausada.")
        return
    # La lógica real de bloqueo se maneja en ejecutar_simulacion
    bloqueo_solicitado = True
    update_console(f"[Sistema] Solicitud de BLOQUEO para {proceso_actual_en_cpu.id}.", "sistema_advertencia")


def desbloquear_proceso():
    """Desbloquea el primer proceso en la cola de bloqueados y lo re-encola a su cola original."""
    if not cola_bloqueados:
        messagebox.showinfo("Nada que desbloquear", "No hay procesos bloqueados para desbloquear.")
        return

    proceso = cola_bloqueados.pop(0) # Sacar el primer proceso bloqueado (FIFO)
    # Su nueva llegada será el tiempo actual de la CPU
    proceso.t_llegada = cpu_tiempo_actual 
    
    with procesos_por_llegar_lock:
        procesos_por_llegar.append(proceso)
        procesos_por_llegar.sort(key=lambda p: p.t_llegada) # Reordenar por tiempo de llegada

    update_console(f"[Sistema] Proceso {proceso.id} ({proceso.queue_type}) DESBLOQUEADO y reencolado en t={cpu_tiempo_actual:.1f}s", "sistema_nuevo_proceso")
    actualizar_vista_cola_procesos()
    actualizar_tabla_rr_queue()
    actualizar_tabla_fcfs_queue()
    actualizar_tabla_pq_queue()


def iniciar_simulacion_hilo():
    """
    Prepara e inicia la simulación Multi-Cola en un hilo separado
    para no bloquear la interfaz de usuario.
    """
    global simulacion_activa, simulacion_pausada, hilo_simulacion, procesos_por_llegar, gantt_process_y_mapping, next_gantt_y_offset, cpu_tiempo_actual, procesos_ejecutados_completos, fragmentos_ejecucion
    global cola_rr, cola_fcfs, cola_pq # Acceder a las colas globales
    
    # Validar el valor del quantum
    q_str = entry_quantum.get().strip()
    try:
        q = float(q_str)
        if q <= 0:
            raise ValueError
    except ValueError:
        messagebox.showerror("Error de Entrada", "El cuantum debe ser un número positivo (entero o decimal).")
        return

    global quantum_value
    quantum_value = q
    entry_quantum.config(state=tk.DISABLED) # Deshabilitar edición del quantum durante la simulación

    if not master_procesos:
        messagebox.showwarning("Sin Procesos", "Agregue al menos un proceso para iniciar la simulación.")
        return
    if simulacion_activa: # Evitar iniciar múltiples simulaciones
        return

    # Reiniciar estados globales para una nueva simulación
    cpu_tiempo_actual = 0.0
    procesos_ejecutados_completos.clear() # Limpiar resultados completos
    cola_rr = ListaCircular() # Reiniciar la lista circular
    cola_fcfs.clear() # Limpiar la cola FCFS
    cola_pq.clear() # Limpiar la cola PQ
    cola_bloqueados.clear() # Limpiar la cola de bloqueados

    with procesos_por_llegar_lock:
        # Crear nuevas instancias de procesos para evitar modificar los originales de master_procesos
        # y asegurar que cada simulación comience con procesos "frescos"
        procesos_por_llegar[:] = []
        for p_original in master_procesos:
            p_copy = Proceso(p_original.id, p_original.original_at, p_original.original_bt,
                            p_original.priority, p_original.queue_type) # Copiar prioridad y tipo de cola
            procesos_por_llegar.append(p_copy)
        procesos_por_llegar.sort(key=lambda p: p.t_llegada) # Ordenar por tiempo de llegada

    gantt_process_y_mapping.clear() # Limpiar mapeo del Gantt
    next_gantt_y_offset = 0
    fragmentos_ejecucion.clear() # Limpiar fragmentos del Gantt y tabla detallada

    canvas_gantt.delete("all") # Limpiar el canvas del Gantt
    
    # Configurar las columnas de la tabla de resultados para incluir "Tipo Cola"
    tree_resultados['columns'] = ("ID", "AT", "BT", "Tipo Cola", "Inicio", "Fin", "Duración", "Espera Fragmento")
    tree_resultados.heading("ID", text="Proceso")
    tree_resultados.heading("AT", text="T llegada")
    tree_resultados.heading("BT", text="Ráfaga")
    tree_resultados.heading("Tipo Cola", text="Tipo Cola")
    tree_resultados.heading("Inicio", text="T Comienzo")
    tree_resultados.heading("Fin", text="T final")
    tree_resultados.heading("Duración", text="T retorno")
    tree_resultados.heading("Espera Fragmento", text="T Espera")
    for col in ("ID", "AT", "BT", "Tipo Cola", "Inicio", "Fin", "Duración", "Espera Fragmento"):
        tree_resultados.column(col, width=80, anchor="center")

    actualizar_tabla_resultados([]) # Limpiar y actualizar la tabla de resultados (fragmentos)
    dibujar_linea_tiempo_gantt() # Redibujar línea de tiempo inicial del Gantt
    actualizar_vista_cola_procesos() # Actualizar vista de colas
    actualizar_tabla_rr_queue() # Actualizar la tabla de la cola RR
    actualizar_tabla_fcfs_queue() # Actualizar la tabla de la cola FCFS
    actualizar_tabla_pq_queue() # Actualizar la tabla de la cola PQ
    label_promedios.config(text="Promedio TAT (Proceso Completo): N/A | Promedio WT (Proceso Completo): N/A")


    simulacion_activa = True
    simulacion_pausada = False
    
    # Deshabilitar / Habilitar botones según el estado de la simulación
    btn_iniciar.config(state=tk.DISABLED)
    btn_pausar_reanudar.config(text="Pausar", state=tk.NORMAL)
    btn_reiniciar.config(state=tk.NORMAL)
    btn_bloquear.config(state=tk.NORMAL)
    btn_desbloquear.config(state=tk.NORMAL)

    update_console(f"[Sistema] Iniciando simulación Multi-Cola con Quantum = {quantum_value:.1f}u...", "sistema")
    # Iniciar la simulación en un hilo separado
    hilo_simulacion = threading.Thread(target=ejecutar_simulacion, daemon=True)
    hilo_simulacion.start()

def pausar_reanudar_simulacion_ui():
    """Alterna el estado de pausa/reanudación de la simulación."""
    global simulacion_pausada
    simulacion_pausada = not simulacion_pausada
    if simulacion_pausada:
        btn_pausar_reanudar.config(text="Reanudar")
        update_console("[Sistema] Simulación PAUSADA.", "pausa")
    else:
        btn_pausar_reanudar.config(text="Pausar")
        update_console("[Sistema] Simulación REANUDADA.", "sistema")

def reiniciar_simulacion():
    """Reinicia completamente el simulador a su estado inicial."""
    global simulacion_activa, simulacion_pausada, hilo_simulacion
    global cola_rr, cola_fcfs, cola_pq # Acceder a las colas globales
    
    simulacion_activa = False # Detener la simulación si está corriendo
    simulacion_pausada = False # Asegurar que no quede en pausa

    # Esperar un breve momento para que el hilo de simulación pueda terminar
    if hilo_simulacion and hilo_simulacion.is_alive():
        time.sleep(0.2) 
    
    # Limpiar todas las estructuras de datos globales
    master_procesos.clear()
    procesos_ejecutados_completos.clear()
    cola_rr = ListaCircular() # Reinicializar la lista circular
    cola_fcfs.clear() # Limpiar la cola FCFS
    cola_pq.clear() # Limpiar la cola PQ
    with procesos_por_llegar_lock:
        procesos_por_llegar.clear()
    cola_bloqueados.clear() # Limpiar la cola de bloqueados

    gantt_process_y_mapping.clear()
    global next_gantt_y_offset, cpu_tiempo_actual
    next_gantt_y_offset = 0
    cpu_tiempo_actual = 0.0
    fragmentos_ejecucion.clear() # Limpiar los fragmentos dibujados en el Gantt

    canvas_gantt.delete("all") # Borrar todo el contenido del Gantt
    dibujar_linea_tiempo_gantt() # Redibujar el eje de tiempo del Gantt
    actualizar_vista_cola_procesos() # Actualizar la vista de las colas
    
    # Resetear las columnas del Treeview a su estado inicial (con Tipo Cola)
    tree_resultados['columns'] = ("ID", "AT", "BT", "Tipo Cola", "Inicio", "Fin", "Duración", "Espera Fragmento")
    tree_resultados.heading("ID", text="Proceso")
    tree_resultados.heading("AT", text="T llegada")
    tree_resultados.heading("BT", text="Ráfaga")
    tree_resultados.heading("Tipo Cola", text="Tipo Cola")
    tree_resultados.heading("Inicio", text="T Comienzo")
    tree_resultados.heading("Fin", text="T final")
    tree_resultados.heading("Duración", text="T retorno")
    tree_resultados.heading("Espera Fragmento", text="T Espera")
    for col in ("ID", "AT", "BT", "Tipo Cola", "Inicio", "Fin", "Duración", "Espera Fragmento"):
        tree_resultados.column(col, width=80, anchor="center")
    actualizar_tabla_resultados([]) # Limpiar y actualizar la tabla de resultados (fragmentos)
    
    # Limpiar las nuevas tablas de cola
    actualizar_tabla_rr_queue()
    actualizar_tabla_fcfs_queue()
    actualizar_tabla_pq_queue()

    # Limpiar la consola
    consola_text.config(state='normal')
    consola_text.delete(1.0, tk.END)
    consola_text.config(state='disabled')
    label_promedios.config(text="Promedio TAT (Proceso Completo): N/A | Promedio WT (Proceso Completo): N/A") # Restablecer promedios

    # Habilitar/Deshabilitar botones para el estado inicial
    btn_agregar.config(state=tk.NORMAL)
    btn_iniciar.config(state=tk.DISABLED)
    btn_pausar_reanudar.config(state=tk.DISABLED, text="Pausar")
    btn_reiniciar.config(state=tk.NORMAL) # Siempre accesible para reiniciar
    entry_quantum.config(state=tk.NORMAL)
    #btn_bloquear.config(state=tk.DISABLED)
    #btn_desbloquear.config(state=tk.DISABLED)

    update_console("Simulador reiniciado. Agregue nuevos procesos para comenzar.", "sistema_advertencia")

def desactivar_controles_simulacion():
    """Desactiva los controles de simulación cuando esta ha finalizado o se ha detenido."""
    global simulacion_activa
    simulacion_activa = False
    btn_pausar_reanudar.config(state=tk.DISABLED, text="Pausar")
"""    btn_bloquear.config(state=tk.DISABLED)
    btn_desbloquear.config(state=tk.DISABLED)"""

# --- INTERFAZ GRÁFICA (UI) ---
root = tk.Tk()
root.title("Simulador de Planificación Multi-Cola")
root.geometry("1100x950") # Ajustar tamaño para acomodar más información
root.configure(bg="#f0f0f0") # Fondo gris claro

# Estilo para Treeview (tabla de resultados)
style = ttk.Style()
style.theme_use("clam") # Un tema más moderno para ttk
style.configure("Treeview.Heading", font=("Arial", 10, "bold"), background="#d0d0d0", foreground="black")
style.configure("Treeview", font=("Arial", 9), rowheight=25, background="white", fieldbackground="white", foreground="black")
style.map("Treeview", background=[('selected', '#a0a0ff')]) # Color de selección

# Crear un Canvas principal para hacer todo el contenido scrollable
outer_canvas = tk.Canvas(root, bg="#f0f0f0")
outer_canvas.pack(side="left", fill="both", expand=True)

# Añadir barras de desplazamiento al Canvas principal
scrollbar_y = ttk.Scrollbar(root, orient="vertical", command=outer_canvas.yview)
scrollbar_y.pack(side="right", fill="y")
outer_canvas.configure(yscrollcommand=scrollbar_y.set)

scrollbar_x = ttk.Scrollbar(root, orient="horizontal", command=outer_canvas.xview)
scrollbar_x.pack(side="bottom", fill="x")
outer_canvas.configure(xscrollcommand=scrollbar_x.set)

# Crear un Frame dentro del Canvas para contener todo el contenido de la aplicación
scrollable_frame = tk.Frame(outer_canvas, bg="#f0f0f0")
outer_canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")

# Configurar el Canvas para que su región de desplazamiento se ajuste al tamaño del frame interno
def _on_frame_configure(event):
    outer_canvas.configure(scrollregion=outer_canvas.bbox("all"))
scrollable_frame.bind("<Configure>", _on_frame_configure)

# Asegurarse de que el frame interno se expanda horizontalmente con el canvas
outer_canvas.bind("<Configure>", lambda e: outer_canvas.itemconfig(outer_canvas.winfo_children()[0], width=e.width))


# --- SECCIÓN SUPERIOR: Entrada y Controles (ahora dentro de scrollable_frame) ---
top_frame = tk.Frame(scrollable_frame, bg="#f0f0f0")
top_frame.pack(fill=tk.X, pady=(0, 10))

# Entrada de procesos
input_frame = tk.LabelFrame(top_frame, text="Añadir Proceso", bg="white", font=("Arial", 11, "bold"), bd=2, relief="groove")
input_frame.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5), ipady=5)

tk.Label(input_frame, text="ID:", bg="white").grid(row=0, column=0, padx=5, pady=5, sticky="w")
entry_pid = tk.Entry(input_frame, width=10, relief="solid", bd=1)
entry_pid.grid(row=0, column=1, padx=5, pady=5)

tk.Label(input_frame, text="Llegada (AT):", bg="white").grid(row=0, column=2, padx=5, pady=5, sticky="w")
entry_at = tk.Entry(input_frame, width=10, relief="solid", bd=1)
entry_at.grid(row=0, column=3, padx=5, pady=5)

tk.Label(input_frame, text="Ráfaga (BT):", bg="white").grid(row=0, column=4, padx=5, pady=5, sticky="w")
entry_bt = tk.Entry(input_frame, width=10, relief="solid", bd=1)
entry_bt.grid(row=0, column=5, padx=5, pady=5)

tk.Label(input_frame, text="Prioridad PQ:", bg="white").grid(row=0, column=6, padx=5, pady=5, sticky="w")
entry_priority_pq = tk.Entry(input_frame, width=10, relief="solid", bd=1)
entry_priority_pq.grid(row=0, column=7, padx=5, pady=5)
 # Deshabilitado por defecto

# Nueva fila para Tipo de Cola y Quantum
tk.Label(input_frame, text="Tipo de Cola:", bg="white").grid(row=1, column=0, padx=5, pady=5, sticky="w")
queue_type_options = ["Aleatorio", "RR", "FCFS", "PQ"]
combo_queue_type = ttk.Combobox(input_frame, values=queue_type_options, state="readonly", width=10)
combo_queue_type.set("Aleatorio") # Valor predeterminado
combo_queue_type.grid(row=1, column=1, padx=5, pady=5, sticky="w")

tk.Label(input_frame, text="Quantum:", bg="white").grid(row=1, column=2, padx=5, pady=5, sticky="w")
entry_quantum = tk.Entry(input_frame, width=10, relief="solid", bd=1)
entry_quantum.insert(0, "2.0") # Valor predeterminado del quantum
entry_quantum.grid(row=1, column=3, padx=5, pady=5)


def on_queue_type_change(event):
    if combo_queue_type.get() == "PQ":
        entry_priority_pq.config(state=tk.NORMAL)
    else:
        entry_priority_pq.delete(0, tk.END)
        entry_priority_pq.config(state=tk.DISABLED)

combo_queue_type.bind("<<ComboboxSelected>>", on_queue_type_change)

btn_agregar = tk.Button(input_frame, text="Añadir Proceso", command=agregar_proceso, bg="#6cbafa", fg="white", font=("Arial", 10, "bold"), relief="raised", bd=2)
btn_agregar.grid(row=1, column=4, columnspan=2, padx=10, pady=5) # columnspan para que ocupe más espacio

# Controles de simulación
control_frame = tk.LabelFrame(top_frame, text="Controles de Simulación", bg="white", font=("Arial", 11, "bold"), bd=2, relief="groove")
control_frame.pack(side=tk.RIGHT, padx=(5, 0), ipady=5)

btn_bloquear = tk.Button(control_frame, text="Bloquear CPU", command=bloquear_proceso_actual, bg="#ff9f4d", fg="white", font=("Arial", 10, "bold"), relief="raised", bd=2, width=10, state=tk.DISABLED)
btn_bloquear.pack(side=tk.LEFT, padx=5, pady=5)

btn_desbloquear = tk.Button(control_frame, text="Desbloquear Sig.", command=desbloquear_proceso, bg="#6cbafa", fg="white", font=("Arial", 10, "bold"), relief="raised", bd=2, width=12, state=tk.DISABLED)
btn_desbloquear.pack(side=tk.LEFT, padx=5, pady=5)

btn_iniciar = tk.Button(control_frame, text="Iniciar", command=iniciar_simulacion_hilo, 
                        state=tk.DISABLED, bg="#4CAF50", fg="white", font=("Arial", 10, "bold"), relief="raised", bd=2, width=8)
btn_iniciar.pack(side=tk.LEFT, padx=5, pady=5)

btn_pausar_reanudar = tk.Button(control_frame, text="Pausar", command=pausar_reanudar_simulacion_ui, 
                                state=tk.DISABLED, bg="#ffcd47", fg="black", font=("Arial", 10, "bold"), relief="raised", bd=2, width=8)
btn_pausar_reanudar.pack(side=tk.LEFT, padx=5, pady=5)

btn_reiniciar = tk.Button(control_frame, text="Reiniciar", command=reiniciar_simulacion, 
                          bg="#FF5733", fg="white", font=("Arial", 10, "bold"), relief="raised", bd=2, width=8)
btn_reiniciar.pack(side=tk.LEFT, padx=5, pady=5)

# --- SECCIÓN MEDIA: Cola y Gantt (ahora dentro de scrollable_frame) ---
middle_frame = tk.Frame(scrollable_frame, bg="#f0f0f0")
middle_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))

# Cola de procesos
cola_frame = tk.LabelFrame(middle_frame, text="Estado de Procesos", bg="white", font=("Arial", 11, "bold"), bd=2, relief="groove", width=280)
cola_frame.pack(side=tk.LEFT, fill=tk.BOTH, padx=(0, 5), expand=False)
cola_frame.pack_propagate(False)

frame_cola_listos = tk.Frame(cola_frame, bg="white")
frame_cola_listos.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

# Gráfico de Gantt
gantt_frame = tk.LabelFrame(middle_frame, text="Gráfico de Gantt", bg="white", font=("Arial", 11, "bold"), bd=2, relief="groove")
gantt_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(5, 0))

canvas_gantt = tk.Canvas(gantt_frame, bg="white", height=150, bd=0, highlightthickness=0)
canvas_gantt.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

# --- SECCIÓN INFERIOR: Resultados y Consola (ahora dentro de scrollable_frame) ---
bottom_frame = tk.Frame(scrollable_frame, bg="#f0f0f0")
bottom_frame.pack(fill=tk.BOTH, expand=True)

# Resultados
results_frame = tk.LabelFrame(bottom_frame, text="Resultados de Ejecución", bg="white", font=("Arial", 11, "bold"), bd=2, relief="groove")
results_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 5))

# Definir las columnas de la tabla de resultados, incluyendo "Tipo Cola"
tree_resultados = ttk.Treeview(results_frame, columns=("ID", "AT", "BT", "Tipo Cola", "Inicio", "Fin", "Duración", "Espera Fragmento"), show="headings", height=8)
tree_resultados.heading("ID", text="Proceso")
tree_resultados.heading("AT", text="T llegada")
tree_resultados.heading("BT", text="Ráfaga")
tree_resultados.heading("Tipo Cola", text="Tipo Cola")
tree_resultados.heading("Inicio", text="T Comienzo")
tree_resultados.heading("Fin", text="T final")
tree_resultados.heading("Duración", text="T retorno")
tree_resultados.heading("Espera Fragmento", text="T Espera")

for col in ("ID", "AT", "BT", "Tipo Cola", "Inicio", "Fin", "Duración", "Espera Fragmento"):
    tree_resultados.column(col, width=80, anchor="center")

tree_resultados.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

label_promedios = tk.Label(results_frame, text="Promedio TAT (Proceso Completo): N/A | Promedio WT (Proceso Completo): N/A", 
                            bg="white", font=("Arial", 10, "bold"), fg="#333333")
label_promedios.pack(pady=5)


# --- NUEVAS TABLAS PARA CADA COLA (ahora dentro de scrollable_frame) ---
queue_tables_frame = tk.LabelFrame(bottom_frame, text="Contenido Actual de Colas", bg="#f0f0f0", font=("Arial", 11, "bold"), bd=2, relief="groove")
queue_tables_frame.pack(fill=tk.BOTH, expand=True, pady=(5, 0))

# Frame para las tablas de cola individuales (para organizarlas horizontalmente)
individual_queues_frame = tk.Frame(queue_tables_frame, bg="#f0f0f0")
individual_queues_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

# Tabla para Round Robin
rr_queue_frame = tk.LabelFrame(individual_queues_frame, text="Cola Round Robin (Prioridad 1)", bg="white", font=("Arial", 10, "bold"), bd=1, relief="solid")
rr_queue_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
tree_rr_queue = ttk.Treeview(rr_queue_frame, columns=("ID", "AT", "BT", "Quantum"), show="headings", height=5)
tree_rr_queue.heading("ID", text="ID")
tree_rr_queue.heading("AT", text="Llegada")
tree_rr_queue.heading("BT", text="Ráfaga")
tree_rr_queue.heading("Quantum", text="Quantum")
for col in ("ID", "AT", "BT", "Quantum"):
    tree_rr_queue.column(col, width=60, anchor="center")
tree_rr_queue.pack(fill=tk.BOTH, expand=True)

# Tabla para FCFS
fcfs_queue_frame = tk.LabelFrame(individual_queues_frame, text="Cola FCFS (Prioridad 2)", bg="white", font=("Arial", 10, "bold"), bd=1, relief="solid")
fcfs_queue_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
tree_fcfs_queue = ttk.Treeview(fcfs_queue_frame, columns=("ID", "AT", "BT"), show="headings", height=5)
tree_fcfs_queue.heading("ID", text="ID")
tree_fcfs_queue.heading("AT", text="Llegada")
tree_fcfs_queue.heading("BT", text="Ráfaga")
for col in ("ID", "AT", "BT"):
    tree_fcfs_queue.column(col, width=60, anchor="center")
tree_fcfs_queue.pack(fill=tk.BOTH, expand=True)

# Tabla para Cola de Prioridades
pq_queue_frame = tk.LabelFrame(individual_queues_frame, text="Cola de Prioridades (Prioridad 3)", bg="white", font=("Arial", 10, "bold"), bd=1, relief="solid")
pq_queue_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5, 0))
tree_pq_queue = ttk.Treeview(pq_queue_frame, columns=("ID", "AT", "BT", "Prioridad"), show="headings", height=5)
tree_pq_queue.heading("ID", text="ID")
tree_pq_queue.heading("AT", text="Llegada")
tree_pq_queue.heading("BT", text="Ráfaga")
tree_pq_queue.heading("Prioridad", text="Prioridad")
for col in ("ID", "AT", "BT", "Prioridad"):
    tree_pq_queue.column(col, width=60, anchor="center")
tree_pq_queue.pack(fill=tk.BOTH, expand=True)


# Consola (ahora dentro de scrollable_frame)
console_frame = tk.LabelFrame(bottom_frame, text="Consola del Simulador", bg="white", font=("Arial", 11, "bold"), bd=2, relief="groove")
console_frame.pack(fill=tk.BOTH, expand=True, pady=(5, 0))

consola_text = tk.Text(console_frame, height=6, bg="black", fg="#00FF00", font=("Consolas", 9), 
                      state='disabled', wrap=tk.WORD, relief="solid", bd=1)
consola_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

# Configuración de tags de la consola para colores de texto
consola_text.tag_config("sistema", foreground="#6495ED") # Azul maíz
consola_text.tag_config("sistema_advertencia", foreground="#FFA500") # Naranja
consola_text.tag_config("sistema_nuevo_proceso", foreground="#32CD32") # Verde lima
consola_text.tag_config("ejecucion", foreground="#BA55D3") # Orquídea media
consola_text.tag_config("pausa", foreground="#FF4500") # Rojo anaranjado
consola_text.tag_config("terminado", foreground="#228B22") # Verde bosque
consola_text.tag_config("normal", foreground="#D3D3D3") # Gris claro

# Inicialización de la UI
actualizar_vista_cola_procesos()
dibujar_linea_tiempo_gantt()
actualizar_tabla_rr_queue()
actualizar_tabla_fcfs_queue()
actualizar_tabla_pq_queue()

root.mainloop()
